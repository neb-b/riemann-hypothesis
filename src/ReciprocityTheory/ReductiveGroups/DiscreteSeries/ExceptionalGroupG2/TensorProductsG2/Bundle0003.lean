module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem dc_ee_nodal (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ, ∀ f ∈ tensSub (genSub E V),
      Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id) f = 0 := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨Q, -, hpos, hadj, -⟩ := tens_unitarize dual hσ hD hgap hV hc hVK hW
  obtain ⟨W, hWfd, hVW, hWM, hWst⟩ := dc_ee_fin_stable dual hE hU hV hc hgap
  have hsym := dc_eeF_Qsymm hE dual (casimir_genSub hE hc) hadj
  obtain ⟨B, hB⟩ := dc_symm_nodal hpos hsym (dc_eeF_mem dual) hWM hWfd hWst
  refine ⟨B, ?_⟩
  let K0 : Submodule ℂ (Fin n → D) :=
    LinearMap.ker (Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id)) ⊓ tensSub (genSub E V)
  have hle : tensSub (genSub E V) ≤ K0 := by
    refine dc_tens_gen_le dual (fun f hf => ⟨hB f (hVW hf), hWM (hVW hf)⟩) ?_
    intro a b f hf
    refine ⟨?_, dc_tens_genSub_stable dual a b f hf.2⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [← dc_aeval_intertwine (tensF dual E a b) (eeF dual E) (eeF dual E)
      (fun y => dc_eeF_comm hE dual a b y), hf.1, map_zero]
  exact fun f hf => (hle hf).1

theorem ee_decomp (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ,
      (∀ f ∈ tensSub (genSub E V), ∃ fb : ℝ → (Fin n → D),
        (∀ b, fb b ∈ tensSub (genSub E V) ∧ eeF dual E (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b) ∧
      ∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ) := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  exact ⟨B, dc_lagrange_decomp (dc_eeF_mem dual) hB, dc_lagrange_eig hB⟩

theorem eigenProj_exists (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) :
    ∃ P : Module.End ℂ (Fin n → D), IsGKEndo dual ε σ E (genSub E V) P ∧
      (∀ f ∈ tensSub (genSub E V), P (P f) = P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f) ∧
      ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0 := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  refine ⟨dc_lagProj (eeF dual E) B z, ?_, dc_lagProj_props (dc_eeF_mem dual) hB z⟩
  unfold dc_lagProj
  split_ifs
  · exact dc_isGKEndo_aeval (isGKEndo_eeF hσ hD V dual) _
  · exact dc_isGKEndo_zero'

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccATensWordMem
section
noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def occCoef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)

def tensWord {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    List (Fin n × Fin n) → (Fin n → M) → (Fin n → M)
  | [] => id
  | p :: w => fun f => tensF dual E p.1 p.2 (tensWord dual E w f)

section Ambient

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem occA_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  exact tensor_group_mul_kDiag dual hσ hg hk f

theorem occA_coef_Eab (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (occCoef dual σ η (fun c => (f c : H))) g =
      occCoef dual σ η (fun c => (tensF dual E a b f c : H)) g := by
  exact tensor_coef_Eab_action dual hσ hD η f a b hg

theorem occA_coef_Eword (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (w : List (Fin n × Fin n)) (f : Fin n → D) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (occCoef dual σ η (fun c => (f c : H))) g =
      occCoef dual σ η (fun c => ((tensWord dual E w f c : D) : H)) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (occCoef dual σ η fun c => (f c : H))) g = _
    rw [Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => ih hx) hg]
    exact occA_coef_Eab dual hσ hD η (tensWord dual E w f) p.1 p.2 hg

theorem occA_coef_smooth (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (η f : Fin n → H)
    (hf : ∀ d, IsSmoothVecU ε σ (f d)) : Formalism.REAL.SmoothOnG ε (occCoef dual σ η f) := by
  exact tensor_coef_smooth dual η f hf

theorem occA_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      occCoef dual σ (fun c => (η c : H)) (fun c => (f c : H)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  exact tensor_coef_memLp dual hσ hW η f hη hf

theorem occA_tensWord_mem {V : Submodule ℂ D} (dual : Bool) (w : List (Fin n × Fin n)) :
    ∀ f ∈ tensSub (genSub E V), tensWord dual E w f ∈ tensSub (genSub E V) := by
  intro f hf
  induction w with
  | nil => exact hf
  | cons p w ih => exact tensSub_stable dual p.1 p.2 _ ih

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

