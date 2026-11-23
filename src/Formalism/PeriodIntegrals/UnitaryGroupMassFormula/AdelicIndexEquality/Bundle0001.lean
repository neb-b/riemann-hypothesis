module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def IsQRefl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (s : Uv I v) : Prop :=
  ∃ (P : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    P * P = P ∧ sigV I v α * α = 1 ∧
      (((s : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) = 1 + (α - 1) • P)

def QReflGen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ g : Uv I v, g ∈ Subgroup.closure {s : Uv I v | IsQRefl I v s}

def QReflPow : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ s : Uv I v, IsQRefl I v s →
      ∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowDefs
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  Algebra.TensorProduct.includeLeftRingHom

def TraceInt : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v α * α = 1 →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQEqOneOfMemNormalizer
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

end Delta

end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQOneOfClosure
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open Formalism.MainNotions.S

def ModQHom : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), Commensurated K →
    (∀ x y : G, modQ K (x * y) = modQ K x * modQ K y) ∧ (∀ k ∈ K, modQ K k = 1) ∧
      (∀ x : G, modQ K x = 1 → dIdx K x = dIdx K x⁻¹)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

open Matrix

variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]

def p1 (π : R ≃+* k × k) : R →+* k := (RingHom.fst k k).comp π.toRingHom

def p2 (π : R ≃+* k × k) : R →+* k := (RingHom.snd k k).comp π.toRingHom

theorem ext_p (π : R ≃+* k × k) {r s : R} (h1 : p1 π r = p1 π s) (h2 : p2 π r = p2 π s) : r = s := by
  apply π.injective
  exact Prod.ext h1 h2

theorem mat_ext_p (π : R ≃+* k × k) {M N : Matrix n n R} (h1 : M.map (p1 π) = N.map (p1 π))
    (h2 : M.map (p2 π) = N.map (p2 π)) : M = N := by
  ext i j
  exact ext_p π (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ

theorem p1_sigma_eq_p2 (r : R) : p1 π (σ r) = p2 π r := by
  show (π (σ r)).1 = (π r).2
  rw [hπ]
  rfl

theorem snd_conj (r : R) : p2 π (σ r) = p1 π r := by
  show (π (σ r)).2 = (π r).1
  rw [hπ]
  rfl

theorem map_conjTranspose_fst (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p1 π) = (M.map (p2 π))ᵀ := by
  ext i j
  exact p1_sigma_eq_p2 σ π hπ (M j i)

theorem map_conjTranspose_snd (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p2 π) = (M.map (p1 π))ᵀ := by
  ext i j
  exact snd_conj σ π hπ (M j i)

theorem unitary_iff (J M : Matrix n n R) :
    Formalism.UG.cT σ M * J * M = J ↔
      (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) = J.map (p1 π) ∧
      (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) = J.map (p2 π) := by
  have e1 : (Formalism.UG.cT σ M * J * M).map (p1 π) = (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_fst σ π hπ]
  have e2 : (Formalism.UG.cT σ M * J * M).map (p2 π) = (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_snd σ π hπ]
  constructor
  · intro h
    rw [← e1, ← e2, h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact mat_ext_p π (by rw [e1, h1]) (by rw [e2, h2])

theorem hermitian_map_snd (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) : J.map (p2 π) = (J.map (p1 π))ᵀ := by
  have h := map_conjTranspose_fst σ π hπ J
  rw [hJ] at h
  rw [h, Matrix.transpose_transpose]


omit hπ in
def proj (J : Matrix n n R) : Formalism.UG.UJ σ J →* GL n k :=
  (Units.map ((p1 π).mapMatrix : Matrix n n R →+* Matrix n n k).toMonoidHom).comp (Formalism.UG.UJ σ J).subtype

theorem proj_bijective (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) (hdet : IsUnit J.det) :
    Function.Bijective (proj σ π J) := by
  have hJ1 : IsUnit (J.map (p1 π)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hunit : ∀ x : Formalism.UG.UJ σ J,
      (((x : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) * ((x : GL n R) : Matrix n n R).map (p1 π) =
        J.map (p1 π) :=
    fun x => ((unitary_iff σ π hπ J ((x : GL n R) : Matrix n n R)).1 x.2).1
  have hinv1 : ∀ x : GL n R,
      (x : Matrix n n R).map (p1 π) * ((x⁻¹ : GL n R) : Matrix n n R).map (p1 π) = 1 := by
    intro x
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro g h hgh
    have h1 : ((g : GL n R) : Matrix n n R).map (p1 π) = ((h : GL n R) : Matrix n n R).map (p1 π) :=
      congrArg (fun u : GL n k => (u : Matrix n n k)) hgh
    have h2 : ((g : GL n R) : Matrix n n R).map (p2 π) = ((h : GL n R) : Matrix n n R).map (p2 π) := by
      have hg := hunit g
      have hh := hunit h
      rw [h1] at hg
      have e : (((g : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) =
          (((h : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) := by
        have := congrArg (fun X => X * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R).map (p1 π)) (hg.trans hh.symm)
        simp only [Matrix.mul_assoc, hinv1, Matrix.mul_one] at this
        simpa only [Matrix.mul_assoc] using this
      have e' := congrArg (fun X => X * (J.map (p1 π))⁻¹) e
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1, Matrix.mul_one] at e'
      have := congrArg Matrix.transpose e'
      simpa only [Matrix.transpose_transpose] using this
    exact Subtype.ext (Units.ext (mat_ext_p π h1 h2))
  · intro A
    let J1 : Matrix n n k := J.map (p1 π)
    let A1 : Matrix n n k := (A : Matrix n n k)
    let B : Matrix n n k := (J1 * ((A⁻¹ : GL n k) : Matrix n n k) * J1⁻¹)ᵀ
    let M : Matrix n n R := Matrix.of fun i j => π.symm (A1 i j, B i j)
    have hM1 : M.map (p1 π) = A1 := by
      ext i j
      simp [M, p1]
    have hM2 : M.map (p2 π) = B := by
      ext i j
      simp [M, p2]
    have hJ1' : IsUnit J1.det := hJ1
    have key : Bᵀ * J1 * A1 = J1 := by
      simp only [B, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ1', Units.inv_mul, Matrix.mul_one]
    have hU : Formalism.UG.cT σ M * J * M = J := by
      rw [unitary_iff σ π hπ J M, hM1, hM2, hermitian_map_snd σ π hπ J hJ]
      refine ⟨key, ?_⟩
      have := congrArg Matrix.transpose key
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have hdetM : IsUnit M.det := by
      have h := congrArg Matrix.det hU
      rw [Matrix.det_mul, Matrix.det_mul] at h
      have h' : IsUnit ((Formalism.UG.cT σ M).det * J.det * M.det) := by rw [h]; exact hdet
      exact isUnit_of_mul_isUnit_right h'
    refine ⟨⟨((Matrix.isUnit_iff_isUnit_det M).2 hdetM).unit, hU⟩, ?_⟩
    exact Units.ext hM1

end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

end
end

