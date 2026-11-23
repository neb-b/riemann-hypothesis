module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0065
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousInsK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousABK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def cMF_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ))
def cMF'_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1)) (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ))
theorem cMF_mul_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ c * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c = 1 := by
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L c.1
  have e2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 1 := by
    rw [← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 * -(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ)) +
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1)ᵀ.map (cA σ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, neg_add_cancel]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, e2, e3, Matrix.fromBlocks_one]
theorem continuous_aB_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) :
    Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k (σ := σ) L δ c.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply]
  split_ifs
  · exact Continuous.smul (continuous_snd (X := Fin L.n → AE F E) (Y := AF F))
      (continuous_const (y := inclR (F := F) (E := E) (AF F) δ))
  · exact continuous_const
theorem continuous_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous cM := by
  have hF : ∀ c, inFrame d.b (cM c) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h
  have hN := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hU : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1 :=
    continuous_const.add (hN.comp continuous_fst)
  have hUn : Continuous fun c : (Fin L.n → AE F E) × AF F => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1) :=
    continuous_const.add (hN.comp continuous_fst.neg)
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hA := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_aB_k (σ := σ) L δ
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hU hA continuous_const (hcA.comp hUn.matrix_transpose)
  have hc' : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hUn ((hUn.matrix_mul hA).matrix_mul (hcA.comp hU.matrix_transpose)).neg
      continuous_const (hcA.comp hU.matrix_transpose)
  have h1 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun c => incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF'_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun c => ?_
    show _ = mat2 (cM c)
    rw [kunf.matrix_eq_inFrame_conj d.b, hF c]
  · refine h2.congr fun c => ?_
    show _ = mat2 (cM c)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hF c, Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cMF_mul_k L δ c)]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinHalfPlaneHolds
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_half_plane_holds : _root_.SiegelEisensteinSeries.EisHalf_k := by
  first | exact @_root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | exact _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k | (intros; apply _root_.GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinitePlacesIntegralMemNhdsOne
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private def fixG_pk {R : Type} [Ring R] (σ : E →ₐ[F] E) (X : Spc F E n) (f : AE F E →+* R) : Subgroup (UA σ X.J) where
  carrier := {g | (mat g).map f = 1}
  one_mem' := Matrix.map_one f (map_zero _) (map_one _)
  mul_mem' := fun {a b} ha hb => by
    show (mat (a * b)).map f = 1
    rw [Euler.mm, Matrix.map_mul]
    exact (congrArg₂ (· * ·) ha hb).trans (mul_one _)
  inv_mem' := fun {a} ha => by
    have e : (mat a⁻¹).map f * (mat a).map f = 1 := by
      rw [← Matrix.map_mul, ← Euler.mm, inv_mul_cancel]
      exact Matrix.map_one f (map_zero _) (map_one _)
    rw [show (mat a).map f = 1 from ha, mul_one] at e
    exact e
private theorem gOff_parts_pk {S : Finset (Pl F)} {c : UA σ X.J} (h : c ∈ gOff σ X S) :
    (∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1) ∧ ∀ v ∈ S, OffAt v c := by
  constructor
  · intro w
    have : gOff σ X S ≤ fixG_pk σ X (compInf F E w : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.1 w
    exact this h
  · intro v hv
    have : gOff σ X S ≤ fixG_pk σ X (compFin F E v : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.2 v hv
    exact this h
private theorem eq_one_of_parts_pk {c : UA σ X.J} (h1 : ∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1)
    (h2 : ∀ v, OffAt v c) : c = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show mat c = 1
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.SWOpFin.tens_eq_zero_of_comp (fun v => ?_) (fun w => ?_))
  · have e : (mat c).map (compFin F E v) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) := by
      rw [Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
      exact h2 v
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
  · have e : (mat c).map (compInf F E w) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compInf F E w) := by
      rw [Matrix.map_one (compInf F E w) (map_zero _) (map_one _)]
      exact h1 w
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
end SlopeTestRemainingChoices
theorem UpperTheory.exists_finite_places_integral_mem_nhds_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}, _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → IsCompact {g : UA σ X.J | IntAll g} → (∀ S, IsClosed (gOff σ X S : Set (UA σ X.J))) → ∀ {N : Set (UA σ X.J)}, N ∈ 𝓝 (1 : UA σ X.J) → ∃ S₀ : Finset (Pl F), ∀ c ∈ gOff σ X S₀, IntAll c → c ∈ N := by
  intro F E _ _ _ _ _ σ B n X _ _ hK hC N hN
  classical
  have hs : IsCompact ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) := hK.inter_right isOpen_interior.isClosed_compl
  have anti : ∀ {S T : Finset (Pl F)}, S ⊆ T → (gOff σ X T : Set (UA σ X.J)) ⊆ gOff σ X S := fun {S T} h =>
    Subgroup.closure_mono fun g hg => ⟨hg.1, fun v hv => hg.2 v (h hv)⟩
  have hd : Directed (· ⊇ ·) (fun S : Finset (Pl F) => (gOff σ X S : Set (UA σ X.J))) := fun S T =>
    ⟨S ∪ T, anti Finset.subset_union_left, anti Finset.subset_union_right⟩
  have hi : ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ ⋂ S : Finset (Pl F), (gOff σ X S : Set (UA σ X.J)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun c hc => ?_
    have h := Set.mem_iInter.1 hc.2
    have e : c = 1 := eq_one_of_parts_pk (gOff_parts_pk (h ∅)).1
      fun v => (gOff_parts_pk (h {v})).2 v (Finset.mem_singleton_self v)
    exact hc.1.2 (e ▸ mem_interior_iff_mem_nhds.2 hN)
  obtain ⟨S, hS⟩ := hs.elim_directed_family_closed _ hC (Set.disjoint_iff_inter_eq_empty.mpr hi) hd
  refine ⟨S, fun c hc hI => ?_⟩
  by_contra hn
  have hm : c ∈ ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ (gOff σ X S : Set (UA σ X.J)) :=
    ⟨⟨hI, fun h => hn (interior_subset h)⟩, hc⟩
  exact Set.disjoint_left.mp hS hm.1 hm.2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsSplitFunctionalDoubled
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_split_functional_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  first | exact @_root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | exact _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k | (intros; apply _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LamMapK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem pEquiv_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β ∈ L.ratV ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β ∈ fA F) ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨P, h1, h2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pEquiv0_k L h.δ0 ⟨cM (0, 1), by
    obtain ⟨A', hA'⟩ := h.cf (0, 1)
    refine ⟨A', ?_⟩
    rw [hA']
    have hu : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (0 : Fin L.n → AE F E) = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k]
    rw [hu]⟩
  exact ⟨P, h1, h2⟩
theorem lam_map_k {lam : Measure (nA σ d.Y d.b)} [lam.IsAddHaarMeasure] {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure]
    {lam' : Measure (nA σ L.Y L.b)} [lam'.IsAddHaarMeasure] (P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ lam.map P = c • ((ν.prod (lamA F)).prod lam') := by
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI : (lam.map P).IsAddHaarMeasure := P.isAddHaarMeasure_map lam
  haveI : SFinite ν := inferInstance
  haveI : SFinite lam' := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : SFinite (ν.prod (lamA F)) := inferInstance
  haveI : ((ν.prod (lamA F)).prod lam').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor (lam.map P) ((ν.prod (lamA F)).prod lam') : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
theorem kap_eq_k {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure] {κ : Measure ((Fin L.n → AE F E) × AF F)}
    [κ.IsAddHaarMeasure] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ κ = c • (ν.prod (lamA F)) := by
  haveI : SFinite ν := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor κ (ν.prod (lamA F)) : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _
end PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C5
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutSerA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
open scoped ContDiff
namespace SerA
theorem sig_sig'_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem chi_add_lat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hw : w + sgOF σ w = 1) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) (x : WOF F E nS nT) :
    phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ x u) * chiLatF σ JS JT ξ₀ B.ψ Λ w (x + u)) =
      chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have e : finIdem F E • (x + (u : WOF F E nS nT)) = finIdem F E • x + u := by
    rw [smul_add, finIdem_smul_of_fin u.fin]
  have e2 : B.ψ (symplOHF σ JS JT ξ₀ x u) = B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • x) u) := by
    have hx := finIdem_add_iota C.chart x
    have h3 := _root_.PositivityTheory.ThKW.beta_iota_left_k C (piWF θ x) (u : WOF F E nS nT)
    rw [piWF_fin u.fin, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h3
    conv_lhs => rw [hx]
    rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul, h3, mul_one]
  unfold chiLatF
  rw [e, e2]
  have hy := finIdem_smul_fin (F := F) (E := E) x
  generalize finIdem F E • x = y at hy ⊢
  by_cases h : y ∈ latOF F E nS nT Λ
  · rw [if_pos h, if_pos (add_mem h hu)]
    have h0 : B.ψ (symplOF σ JS JT ξ₀ (intAF F w • y) u) = 1 :=
      (hA _).1 ((latF F E nS nT Λ).smul_mem w (show XFF.mk y hy ∈ latF F E nS nT Λ from h)) u hu
    rw [phaseF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad hσ C.hS C.hT C.hξ hw,
      AddChar.map_add_eq_mul, h0, mul_one]
  · have h2 : y + (u : WOF F E nS nT) ∉ latOF F E nS nT Λ := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu)
      rwa [add_sub_cancel_right] at h3)
    rw [if_neg h, if_neg h2, mul_zero, mul_zero]
theorem main_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) := by
  have hσ := _root_.PositivityTheory.ThKW.SerA.sig_sig'_k C.good
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1
  have hA := hO.sd
  have hw := hO.hw
  obtain ⟨-, hJ, hsym, hpos⟩ := omV_laws
    (_root_.PositivityTheory.ThKW.hermitian_form_selfadjoint_global F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ).1 hs.sq hs.pos
  have hl : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ (x + y) z) =
      B.ψ (symplOHF σ JS JT ξ₀ x z) * B.ψ (symplOHF σ JS JT ξ₀ y z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x (y + z)) =
      B.ψ (symplOHF σ JS JT ξ₀ x y) * B.ψ (symplOHF σ JS JT ξ₀ x z) :=
    fun x y z => by rw [GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ x : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x x) = 1 := fun x => by
    rw [symplOHF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WOF F E nS nT) (v : IxF F nS nT → ℂ), B.ψ (symplOHF σ JS JT ξ₀ x (iotaA ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWA θ x) v : ℝ)) :=
    fun x v => _root_.PositivityTheory.ThKW.beta_iota_right_k C x v
  have fl : ∀ u ∈ latF F E nS nT Λ, ∀ x : WOF F E nS nT, phaseF σ JS JT ξ₀ B.ψ w u *
      (B.ψ (symplOHF σ JS JT ξ₀ x u) * serF σ JS JT ξ₀ B θ ι s Λ w a (x + u)) = serF σ JS JT ξ₀ B θ ι s Λ w a x :=
    fun u hu x => GlobalTheory.GaussSeriesVacuum.series_inv_scalar (G := WOF F E nS nT)
      (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) hl hr hd hβ a u (piWF_fin u.fin) _ (_root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw hu) x
  obtain ⟨U, hUo, hlev⟩ := exists_level (F := F) (E := E) (nS := nS) (nT := nT) hG 2 two_pos
  let U₀ : AddSubgroup (WOF F E nS nT) :=
    (latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E))
  obtain ⟨fc, fs, fv⟩ := GlobalTheory.GaussSeriesVacuum.series_regular (piWA θ) (iotaA ι)
    (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) U₀ U
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) (_root_.PositivityTheory.ThKW.continuous_piWF_k C) (continuous_iotaVF C.chart) (piWF_iotaVF C.chart) hl hr hd
    (fun x y => hψ.2.1 _)
    (hψ.1.comp (GlobalTheory.RealWeilF.continuous_symplOHF σ JS JT ξ₀ continuous_fst continuous_snd)) hβ hJ hsym hpos
    (by
      rintro _ ⟨y, rfl⟩ h
      have e : piWF θ (ratWF (F := F) y) = 0 := h
      rw [_root_.PositivityTheory.ThKW.piWF_ratWF_k C] at e
      have : y = 0 := infRatF_injective B (by rw [e, map_zero])
      subst this
      exact map_zero _)
    (fun R => by
      refine ((_root_.PositivityTheory.ThKW.finite_lat_k C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      refine ⟨y, ⟨(_root_.PositivityTheory.ThKW.finRatF_mem_iff_k C hG hR hA y).1 h1, ?_⟩, rfl⟩
      have e : piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := _root_.PositivityTheory.ThKW.piWF_ratWF_k C y
      rw [← e]
      exact h2)
    (fun x hx => by unfold chiLatF; exact if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · rw [norm_zero]; exact zero_le_one)
    (fun x v => by
      show chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = _
      unfold chiLatF
      rw [smul_add, finIdem_smul_of_real (real_iotaVF C.chart v), add_zero])
    hUo
    (fun u hu x => by
      obtain ⟨l, hl', e⟩ := hlev u hu
      have e3 : u - iotaA ι (piWA θ u) = ((2 • l : XFF F E nS nT) : WOF F E nS nT) :=
        (sub_eq_of_eq_add (finIdem_add_iota C.chart u)).trans e
      rw [e3]
      have e2 := _root_.PositivityTheory.ThKW.SerA.chi_add_lat_k C hA hw (nsmul_mem hl' 2) x
      rw [phase_two' hA w hl', one_mul] at e2
      exact e2) a
  have hquasi : ∀ (γ : Matrix (Fin nT) (Fin nS) E) (x : WOF F E nS nT),
      serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x)) * serF σ JS JT ξ₀ B θ ι s Λ w a x := by
    intro γ x
    have e : B.ψ (symplOHF σ JS JT ξ₀ (ratWF γ) x) * serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        serF σ JS JT ξ₀ B θ ι s Λ w a x :=
      GlobalTheory.HeisenbergGaussianSeries.series_quasi (G := WOF F E nS nT) (p := piWA θ) (ι := iotaA ι)
        (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (om := omV (HMF JS JT ξ₀ (tauB B))) (J := jV s)
        (Γ := ratLF F E nS nT) (χ := chiLatF σ JS JT ξ₀ B.ψ Λ w) hl hr
        (by rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩; exact _root_.PositivityTheory.ThKW.psi_rat_k C y y') a (ratWF γ) ⟨γ, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hlevel : ∀ u ∈ U, u.map (infPartF F E) = 0 →
      heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w a) = serF σ JS JT ξ₀ B θ ι s Λ w a := by
    intro u hu h
    obtain ⟨l, hl', e⟩ := hlev u hu
    rw [finIdem_smul_of_fin h] at e
    subst e
    funext x
    have e2 := fl _ (nsmul_mem hl' 2) x
    rw [phase_two' hA w hl', one_mul] at e2
    exact e2
  have hsm : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
      ∀ x, ContDiff ℝ ∞ fun t => serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t) := by
    intro k L hL hL0 x
    let c : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) := (piWA θ).comp L
    have hc : Continuous c := (_root_.PositivityTheory.ThKW.continuous_piWF_k C).comp hL
    have hLc : ∀ t, L t = iotaA ι (c t) := fun t => by
      have := finIdem_add_iota C.chart (L t)
      rw [finIdem_smul_of_real (hL0 t), zero_add] at this
      exact this
    have h := (fs x).comp (c.toRealLinearMap hc).contDiff
    refine (congrArg (ContDiff ℝ ∞) (funext fun t => ?_)).mp h
    show _ = serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t)
    rw [hLc t]
    rfl
  refine ⟨⟨hquasi, ⟨U, hUo, hlevel⟩, fc, hsm⟩, fun u hu => Subtype.ext (funext fun x => ?_), fun x z => fv x z⟩
  rw [coe_opFF]
  exact fl u hu x
end SerA
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldHgt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem hgtPull_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.hgtPull_k
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

