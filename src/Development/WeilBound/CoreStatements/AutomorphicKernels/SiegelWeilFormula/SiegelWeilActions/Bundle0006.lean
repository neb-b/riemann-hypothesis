module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisLeftInv
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem phz_leftInv (d : SD σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y) (phz d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp : f (p * g) = f g := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [phz, SD.Ht, ha, hfp]

theorem eis_leftInv (d : SD σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (phz_leftInv d hf z)

theorem fc_dom (d : SD σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  refine h.2.2.1.setIntegral_eq h₀.2.2.1 fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]

end PositivityTheory.SiegelWeilFormula.Act.C1

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsClosedDiagonalStabiliser
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isClosed_diagonal_stabiliser (d : SD σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have hb := d.ok.frame
  have hset : (par2 σ d.Y : Set d.G) = {p | (inFrame d.b p).toBlocks₂₁ = 0} :=
    Set.ext fun p => mem_stabiliser_iff_frame_lower_block hb p
  rw [hset]
  have hm : Continuous (mat2 (σ := σ) (Y := d.Y)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun p : d.G => inFrame d.b p :=
    (continuous_const.matrix_mul hm).matrix_mul continuous_const
  exact isClosed_eq (continuous_matrix fun i j => hc.matrix_elem (Sum.inr i) (Sum.inl j)) continuous_const

theorem continuous_a' (d : SD σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (isClosed_diagonal_stabiliser d) (kunf.isCompact_K d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (kunf.SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (kunf.SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, kunf.SecA.uDet_eq ht]

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

