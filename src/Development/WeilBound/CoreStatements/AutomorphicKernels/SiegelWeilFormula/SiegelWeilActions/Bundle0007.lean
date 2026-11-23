module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousPhz
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_phz (d : SD σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (phz d f s₁ z) := by
  have ha := continuous_a' d
  have e : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) := by
    funext x; rw [kunf.ht_eq]
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [e]
    exact (Complex.continuous_ofReal.comp ha).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (kunf.a_pos d x))
  exact h1.mul hf

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernUniqueness
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def Au {d : SD σ} (L : LD d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne {d : SD σ} (L : LD d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h

theorem Au_mul {d : SD σ} (L : LD d) (u v : Fin L.n → AE F E) : Au L u * Au L v = Au L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (em_ne L j) _
  simp only [Au, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]

theorem Au_zero {d : SD σ} (L : LD d) : Au L 0 = 1 := by simp [Au]

theorem cA_injective (d : SD σ) : Function.Injective (cA σ) := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  have hb : Function.Bijective σ := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective

theorem frame_blk (d : SD σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1

theorem blk_unique (d : SD σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = Matrix.fromBlocks A 0 0 A₁) (hy : inFrame d.b y = Matrix.fromBlocks A 0 0 A₂) : x = y := by
  have h1 := frame_blk d hx
  have h2 := frame_blk d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (cA_injective d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzJLeftInv
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem range_or (L : LD d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩

theorem j_par (L : LD d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases range_or L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases range_or L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp

theorem j_rat (L : LD d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (range_or L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (range_or L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]

theorem phz_j_leftInv (L : LD d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show phz d f s₁ z (L.j (p * g) * x) = phz d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact phz_leftInv d hf z (L.j p) ⟨j_par L hp.1, j_rat L hp.2⟩ _

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end

