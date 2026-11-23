module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDet
section
open UpperTheory.Gal.Gen

open Classical in
private noncomputable def rho0 (H : Type) [Group H] [Fintype H] : H →* Matrix H H ℤ where
  toFun u := Matrix.of fun h g => if h = u * g then 1 else 0
  map_one' := by
    ext h g
    simp [Matrix.one_apply]
  map_mul' u v := by
    ext h g
    have e : ∀ x, (if h = u * x then (1 : ℤ) else 0) * (if x = v * g then 1 else 0)
        = if x = v * g then (if h = u * x then 1 else 0) else 0 := by
      intro x
      split_ifs <;> simp
    simp only [Matrix.mul_apply, Matrix.of_apply, e, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      mul_assoc]

theorem UpperTheory.Gal.Gen.groupDet_pf :
    UpperTheory.Gal.Gen.TriMat → UpperTheory.Gal.Gen.DetLow → UpperTheory.Gal.Gen.GroupDet := by
  classical
  intro hT hD k _ _ l _ H _ _ hp a ρ ha hrank
  obtain ⟨Q, P, hQP⟩ := hT l H hp H (rho0 H)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix H H k, A = Matrix.of fun h g : H => a (h * g⁻¹) := ⟨_, rfl⟩
  rw [← hAdef] at hrank
  obtain ⟨R, hR⟩ : ∃ R : H → Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) ℤ,
      R = fun u => Q * rho0 H u * P := ⟨_, rfl⟩
  have hm : ∀ u i j, ∃ m : ℤ, j ≤ i → R u i j - (if i = j then 1 else 0) = (l : ℤ) * m := by
    intro u i j
    by_cases h : j ≤ i
    · obtain ⟨m, hm⟩ := hQP u i j h
      exact ⟨m, fun _ => by rw [hR]; exact hm⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose m hm using hm
  have hAsum : A = ∑ u, a u • (rho0 H u).map (Int.castRingHom k) := by
    ext h g
    have e : ∀ u : H, h = u * g ↔ u = h * g⁻¹ := fun u => by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    simp [hAdef, Matrix.sum_apply, rho0, e]
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      A' = Q.map (Int.castRingHom k) * A * P.map (Int.castRingHom k) := ⟨_, rfl⟩
  have hA'sum : A' = ∑ u, a u • (R u).map (Int.castRingHom k) := by
    rw [hA'def, hAsum, hR]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul]
  have hA' : ∀ i j, A' i j = ∑ u, a u * ((R u i j : ℤ) : k) := by
    intro i j
    rw [hA'sum]
    simp [Matrix.sum_apply]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (Fintype.card H)) (Fin (Fintype.card H)) k,
      B = Matrix.of fun i j => - ∑ u, a u * ((m u i j : ℤ) : k) := ⟨_, rfl⟩
  have hTe : ∀ i j, j ≤ i → (A' + (l : k) • B) i j = (∑ u, a u) * (if i = j then 1 else 0) := by
    intro i j hij
    have e : ∀ u, ((R u i j : ℤ) : k) = (if i = j then 1 else 0) + (l : k) * ((m u i j : ℤ) : k) := by
      intro u
      have := hm u i j hij
      have h2 : R u i j = (if i = j then 1 else 0) + (l : ℤ) * m u i j := by linarith
      rw [h2]
      push_cast
      rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA', hB, Matrix.of_apply, e,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
    have : ∀ u, a u * ((l : k) * ((m u i j : ℤ) : k)) = (l : k) * (a u * ((m u i j : ℤ) : k)) :=
      fun u => by ring
    simp only [this]
    simp
  have hdet : (A' + (l : k) • B).det = (∑ u, a u) ^ Fintype.card H := by
    rw [Matrix.det_of_upperTriangular]
    · simp [hTe]
    · intro i j hij
      have hji : j < i := hij
      rw [hTe i j hji.le, if_neg hji.ne', mul_zero]
  have hnA : ∀ i j, ‖A' i j‖ ≤ 1 := by
    intro i j
    rw [hA']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnB : ∀ i j, ‖B i j‖ ≤ 1 := by
    intro i j
    rw [hB, Matrix.of_apply, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun u _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ha u) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one k _)
  have hnl : ‖(l : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one k l
  have hr : A'.rank ≤ ρ := by
    rw [hA'def]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrank)
  have := hD k (Fintype.card H) A' B (l : k) ρ hnA hnB hnl hr
  rw [hdet, norm_pow] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HSPf
section
noncomputable section

namespace UpperTheory.Gal.Gen

theorem hS_pf : HS := by
  classical
  intro X _ B V hV
  let L := WithLp.linearEquiv 2 ℂ (X → ℂ)
  let V' : Submodule ℂ (EuclideanSpace ℂ X) := V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)
  have hfr : Module.finrank ℂ V' = Module.finrank ℂ V := LinearEquiv.finrank_map_eq L.symm V
  let e := stdOrthonormalBasis ℂ V'
  let f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X := fun i => (e i : EuclideanSpace ℂ X)
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ
  have hfix : ∀ i x, ∑ y, B x y * f i y = f i x := by
    intro i x
    obtain ⟨v, hv, hvf⟩ := (e i).2
    have h1 : ∀ y, f i y = v y := by
      intro y
      have : f i = L.symm v := hvf.symm
      rw [this]
      rfl
    have h2 := congrFun (hV v hv) x
    simp only [Matrix.mulVec, dotProduct] at h2
    simp only [h1]
    exact h2
  let r : X → EuclideanSpace ℂ X := fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))
  have hinner : ∀ i x, inner ℂ (r x) (f i) = f i x := by
    intro i x
    rw [← hfix i x, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [r, RCLike.inner_apply, mul_comm]
  have hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2 := by
    intro x
    have h := hf.sum_inner_products_le (x := r x) (s := Finset.univ)
    have h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [r]
    rw [h3] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm, hinner]
  have hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1 := by
    intro i
    rw [← EuclideanSpace.norm_sq_eq, hf.1 i]
    simp
  calc (Module.finrank ℂ V : ℝ) = ∑ i : Fin (Module.finrank ℂ V'), ∑ x, ‖f i x‖ ^ 2 := by
        simp [hone, hfr]
    _ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TriMat
section
open UpperTheory.Gal.Gen

private lemma repr_sum_mul {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X]
    (b : Module.Basis ι k (X → k)) (v : X → k) (i : ι) :
    ∑ x, b.repr (Pi.single x 1) i * v x = b.repr v i := by
  have hv : v = ∑ x, v x • (Pi.single x 1 : X → k) := by
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Finsupp.finsetSum_apply, mul_comm]

private lemma conj_apply {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X] [Fintype ι]
    (b : Module.Basis ι k (X → k)) (M : Matrix X X k) (i j : ι) :
    ((Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix ι X k) * M *
      (Matrix.of fun x j => b j x : Matrix X ι k)) i j = b.repr (M.mulVec (b j)) i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← repr_sum_mul b]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem UpperTheory.Gal.Gen.triMat_pf :
    UpperTheory.Gal.Gen.Flag → UpperTheory.Gal.Gen.TriMat := by
  intro hF l _ H _ hH X _ _ ρ
  let ρ' : Representation (ZMod l) H (X → ZMod l) :=
    ((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp
      (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)
  have hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v := by
    intro h v
    rfl
  obtain ⟨b₀, hb₀⟩ := hF l H hH (X → ZMod l) ρ'
  have hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X :=
    Module.finrank_fintype_fun_eq_card _
  let e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X) := finCongr hcard
  let b := b₀.reindex e
  have hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0 := by
    intro h i j hij
    have := hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)
    simpa [b] using this
  let Q : Matrix (Fin (Fintype.card X)) X ℤ := fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)
  let P : Matrix X (Fin (Fintype.card X)) ℤ := fun x j => ((b j x).val : ℤ)
  refine ⟨Q, P, fun h i j hij => ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1
  have hQ : Q.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix _ X (ZMod l)) := by
    ext i x
    change ((((b.repr (Pi.single x 1) i).val : ℤ)) : ZMod l) = b.repr (Pi.single x 1) i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hP : P.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun x j => b j x : Matrix X _ (ZMod l)) := by
    ext x j
    change ((((b j x).val : ℤ)) : ZMod l) = b j x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i := by
    have h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) =
        ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j := rfl
    rw [h1, Matrix.map_mul, Matrix.map_mul, hQ, hP, conj_apply, hρ']
  have hd := hb h i j hij
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply] at hd
  rw [Int.cast_sub, hc, hd]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij', Ne.symm hij']
end

