module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.EqMono
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eqMono_unit {Λ S : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing S] [Algebra Λ S] [IsCO Λ S] {x : S}
    (h : IsUnit (res Λ S x)) : IsUnit x := by
  by_contra hn
  exact h.ne_zero ((res_eq_zero_iff Λ S x).2 hn)

private theorem eqMono_root {S : Type} [CommRing S] (x : S) (c : Fin 4 → S) (i : Fin 4)
    (h : ∏ j, (x - c j) = 0) (hu : ∀ j, j ≠ i → IsUnit (x - c j)) : x = c i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  have h2 : IsUnit (∏ j ∈ Finset.univ.erase i, (x - c j)) :=
    IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj)
  exact sub_eq_zero.1 (h2.mul_left_eq_zero.1 h)

theorem UpperTheory.V.Ws.sxEqMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Ok ((residue Λ).comp a) → Φ.Near a 0 D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → ∀ x ∈ mono D.r 0, ∃ b : W.gr 0, ((b : W.A) : R) = x ∧ f b = f' b := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hOk hNear hGr D' hD' cp hcp R' _ _ _ f f' hff' x hx
  classical
  let φA : W.gr 0 →ₐ[Λ] R :=
    { toRingHom := (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A)
      commutes' := fun c => rfl }
  have hAinj : Function.Injective (algebraMap (W.gr 0) W.A) := fun b c h => Subtype.ext h
  let E : Subring R := (AlgHom.equalizer f f').toSubring.map (φA : W.gr 0 →+* R)
  have hmem : ∀ b : W.gr 0, f b = f' b → φA b ∈ E := fun b hb => Subring.mem_map.mpr ⟨b, hb, rfl⟩
  have hrep := hNear.rep
  have hdex : ∀ i : Fin 4, ∃ d : W.gr 0, φA d = D.r Φ.g0 i i := by
    intro i
    have h := hGr.ent Φ.g0 i i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact ⟨⟨⟨_, W.part_le_A h⟩, h⟩, rfl⟩
  choose d hd using hdex
  have hresd : ∀ i, res Λ (W.gr 0) (d i) = residue Λ (a ↑((Φ.χ i) Φ.g0)) := by
    intro i
    rw [← res_map φA, hd]
    exact hNear.diag Φ.g0 i
  have hdist : ∀ i j, i ≠ j → IsUnit (res Λ (W.gr 0) (d i - d j)) := by
    intro i j hij
    have h := hOk.dist i j hij
    simp only [RingHom.comp_apply] at h
    rw [map_sub, hresd, hresd, ← map_sub]
    exact h
  have hD'r : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := by
    intro g
    rw [← hD']
    rfl
  have hD'g0 : D'.r Φ.g0 = Matrix.diagonal (fun i => algebraMap (W.gr 0) W.A (d i)) := by
    ext i j
    change (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = (W.A.val : W.A →+* R) _
    have h1 : (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = D.r Φ.g0 i j := by
      rw [hD'r]
      rfl
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, h1, ← hd i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, h1]
      exact hrep.nrm hij
  have hcp0 : cp Φ.g0 = ∏ j, (X - C (d j)) := by
    apply Polynomial.map_injective _ hAinj
    rw [hcp, hD'g0, Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp
  have hmapeq : (cp Φ.g0).map (f : W.gr 0 →+* R') = (cp Φ.g0).map (f' : W.gr 0 →+* R') := by
    ext n
    simpa using hff' Φ.g0 n
  have hfix : ∀ i, f (d i) = f' (d i) := by
    intro i
    have hroot : ∏ j, (f' (d i) - f (d j)) = 0 := by
      have h1 : ((cp Φ.g0).map (f' : W.gr 0 →+* R')).eval (f' (d i)) = 0 := by
        rw [hcp0, Polynomial.map_prod, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp
      rw [← hmapeq, hcp0, Polynomial.map_prod, Polynomial.eval_prod] at h1
      simpa using h1
    have hu : ∀ j, j ≠ i → IsUnit (f' (d i) - f (d j)) := by
      intro j hji
      apply eqMono_unit (Λ := Λ)
      rw [map_sub, res_map, res_map, ← map_sub]
      exact hdist i j (Ne.symm hji)
    exact (eqMono_root (f' (d i)) (fun j => f (d j)) i hroot hu).symm
  have hν : ∀ g, ∃ ν ∈ E, IsGSp ν (D.r g) := fun g =>
    ⟨_, hmem (algebraMap Λ (W.gr 0) (a ↑(Φ.ν g))) (by rw [f.commutes, f'.commutes]), hrep.mult g⟩
  have htr : ∀ g, Matrix.trace (D.r g) ∈ E := by
    intro g
    have h2 : Matrix.trace (D'.r g) = algebraMap (W.gr 0) W.A (-(cp g).coeff 3) := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hcp, Polynomial.coeff_map, map_neg]
    have h3 : Matrix.trace (D.r g) = (W.A.val : W.A →+* R) (Matrix.trace (D'.r g)) := by
      rw [hD'r g]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    have h1 : Matrix.trace (D.r g) = φA (-(cp g).coeff 3) := by
      rw [h3, h2]
      rfl
    rw [h1]
    exact hmem _ (by rw [map_neg, map_neg, hff' g 3])
  have hEdiag : ∀ i, D.r Φ.g0 i i ∈ E := fun i => by
    rw [← hd i]
    exact hmem _ (hfix i)
  have hsep : ∀ i j, i ≠ j → ∃ u ∈ E, u * (D.r Φ.g0 i i - D.r Φ.g0 j j) = 1 := by
    intro i j hij
    obtain ⟨U, hU⟩ := eqMono_unit (Λ := Λ) (S := W.gr 0) (hdist i j hij)
    have hfe : f (d i - d j) = f' (d i - d j) := by rw [map_sub, map_sub, hfix, hfix]
    have e1 : f ↑U⁻¹ * f (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have e2 : f' ↑U⁻¹ * f' (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have hinv : f (↑U⁻¹ : W.gr 0) = f' ↑U⁻¹ := by
      calc f ↑U⁻¹ = f ↑U⁻¹ * (f' (d i - d j) * f' ↑U⁻¹) := by rw [mul_comm (f' _), e2, mul_one]
        _ = (f ↑U⁻¹ * f (d i - d j)) * f' ↑U⁻¹ := by rw [hfe]; ring
        _ = f' ↑U⁻¹ := by rw [e1, one_mul]
    refine ⟨φA ↑U⁻¹, hmem _ hinv, ?_⟩
    rw [← hd i, ← hd j, ← map_sub, ← map_mul, ← hU, Units.inv_mul, map_one]
  have hsub := sxMonoZero E D.r Φ.g0 hν htr hrep.nrm hEdiag hsep
  obtain ⟨b, hb, hbx⟩ := Subring.mem_map.mp (hsub hx)
  exact ⟨b, hbx, hb⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SubMemMax
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem char_eq_wv {R : Type} [CommRing R] (t : Multiplicative (ℤ × ℤ) →* Rˣ) (w : ℤ × ℤ) :
    t (Multiplicative.ofAdd w) = wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w := by
  have h : w = w.1 • ((1, 0) : ℤ × ℤ) + w.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp
  conv_lhs => rw [h]
  rw [ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow]
  rfl

private theorem const_mem {Λ X R : Type} [CommRing Λ] [AddCommGroup X] [CommRing R] [Algebra Λ R] (W : WPres Λ X R)
    (c : Λ) : algebraMap Λ R c ∈ W.part 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)

private theorem sub_mem_max {Λ R : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {x : R} {c : Λ} (h : res Λ R x = residue Λ c) : x - algebraMap Λ R c ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff Λ, map_sub, AlgHom.commutes, h]
  exact sub_self _

theorem UpperTheory.V.Ws.sxGradD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R}, Φ.RUniv a D → ∃ W : WPres Λ (ℤ × ℤ) R, D.Graded W := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D hD
  obtain ⟨hN, hU⟩ := hD
  let c : Γ → Fin 4 → Fin 4 → Λ := fun g i j => if i = j then a (Φ.χ i g) else 0
  let S : Type := (Γ × Fin 4 × Fin 4) ⊕ (Σ v : Φ.ι, Fin 4 × Φ.Gv v)
  let e : S → R := Sum.elim (fun x => D.r x.1 x.2.1 x.2.2 - algebraMap Λ R (c x.1 x.2.1 x.2.2))
    (fun x => D.ψ x.1 x.2.1 x.2.2 - algebraMap Λ R (a (Φ.χ x.2.1 x.2.2)))
  let w : S → ℤ × ℤ := Sum.elim (fun x => wt x.2.1 x.2.2) (fun _ => 0)
  have hc : ∀ g i j, i ≠ j → c g i j = 0 := fun g i j h => if_neg h
  refine (coord_grading Λ (ℤ × ℤ) R S e w ?_ ?_ ?_).elim fun W ⟨u, hu, hW⟩ => ?_
  rotate_right
  · refine ⟨W, fun s => ?_, fun g i j => ?_, fun v i s => ?_, fun s => ?_⟩
    · rw [(hu s).1]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
        by_cases h : i = j
        · subst h
          exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
        · rw [hc g i j h, map_zero, sub_zero]
          exact hN.off g i j h le_rfl
      · exact sub_mem_max (hN.redψ v i t)
    · have h1 : D.r g i j - algebraMap Λ R (c g i j) ∈ W.part (wt i j) := hW (Sum.inl (g, i, j))
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        simpa using add_mem h1 (const_mem W (c g i j))
      · rwa [hc g i j h, map_zero, sub_zero] at h1
    · have h1 : D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)) ∈ W.part 0 := hW (Sum.inr ⟨v, i, s⟩)
      simpa using add_mem h1 (const_mem W (a (Φ.χ i s)))
    · rw [(hu s).1, (hu s).2]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · exact Or.inl ⟨g, i, j, c g i j, rfl, rfl, hc g i j⟩
      · exact Or.inr ⟨v, i, t, _, rfl, rfl⟩
  · rintro (⟨g, i, j⟩ | ⟨v, i, t⟩)
    · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
      by_cases h : i = j
      · subst h
        exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
      · rw [hc g i j h, map_zero, sub_zero]
        exact hN.off g i j h le_rfl
    · exact sub_mem_max (hN.redψ v i t)
  · intro R' _ _ _ f f' h
    refine (hU R' (D.map (f' : R →+* R')) (sxNearMap f' hN)).unique ?_ rfl
    refine RD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_) (funext fun v => funext fun i => MonoidHom.ext fun s => ?_)
    · have h1 : f (D.r g i j - algebraMap Λ R (c g i j)) = f' (D.r g i j - algebraMap Λ R (c g i j)) :=
        h (Sum.inl (g, i, j))
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
    · have h1 : f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) = f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) :=
        h (Sum.inr ⟨v, i, s⟩)
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
  · intro R' _ _ _ f t _
    obtain ⟨D', hD', hr, hψ⟩ := sxNearConj (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
      (sxNearMap f hN)
    obtain ⟨f', hf', -⟩ := hU R' D' hD'
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, s⟩)
    · show f' (D.r g i j - algebraMap Λ R (c g i j)) =
        t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j - algebraMap Λ R (c g i j))
      have h1 : f' (D.r g i j) = t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j) := by
        have h2 : f' (D.r g i j) = D'.r g i j := by rw [← hf']; rfl
        rw [h2, hr, char_eq_wv t (wt i j)]
        rfl
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · rw [hc g i j h, map_zero, sub_zero, h1]
    · show f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) =
        t (Multiplicative.ofAdd 0) * f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)))
      have h1 : f' (D.ψ v i s) = f (D.ψ v i s) := by
        have h2 : f' (D.ψ v i s) = D'.ψ v i s := by rw [← hf']; rfl
        rw [h2, hψ]
        rfl
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
      simp
end

