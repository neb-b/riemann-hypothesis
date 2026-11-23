module

public import Development.WeilBound.CoreStatements.ThetaDilations.ParAlg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.ThetaDilations.ContinuousPm
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem exists_anti (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hss : ∀ x, σ (σ x) = x := GlobalTheory.GaussMean.OneVec.sigma_sigma h
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have h2 : σ y = y := by
    by_contra h3
    exact hne (y - σ y) (sub_ne_zero.2 (Ne.symm h3)) (by rw [map_sub, hss, neg_sub])
  have := h.2.2.2 τ y
  rw [h2] at this
  simpa using this.symm

theorem norm_sigR (h : IsCMExt F E σ) (a : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R a) = a * sigR R σ a := by
  have ht : a + sigR R σ a = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) :=
    GlobalTheory.GaussMean.OneVec.add_sigR R h a
  let B := Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h.2.2.1)
  have key : algebraMap R (R ⊗[F] E) (Algebra.norm R a) =
      algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) a) * a - a * a := by
    apply Algebra.leftMulMatrix_injective B
    rw [map_sub, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.norm_eq_matrix_det B,
      Algebra.trace_eq_matrix_trace B]
    generalize Algebra.leftMulMatrix B a = A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply] <;> ring
  rw [key, ← ht]; ring

theorem cT_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

theorem hform_conj {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J : Matrix (Fin M) (Fin M) K} (hs : ∀ x, s (s x) = x)
    (hJ : cT s J = J) (x y : Fin M → K) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hform_add {K : Type} [CommRing K] {M : ℕ} (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J (x + y) (x + y) = hform s J x x + hform s J x y + hform s J y x + hform s J y y := by
  have e : (s : K → K) ∘ (x + y) = s ∘ x + s ∘ y := funext fun _ => map_add s _ _
  simp only [hform_eq, e, Matrix.add_vecMul, add_dotProduct, dotProduct_add]; ring

theorem hform_U {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J)
    (x : Fin M → K) : hform s J (U *ᵥ x) (U *ᵥ x) = hform s J x x := by
  have e : (s : K → K) ∘ (U *ᵥ x) = (s ∘ x) ᵥ* cT s U := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU]

theorem hyp_inv {K : Type} [CommRing K] {M : ℕ} {J Ji : Matrix (Fin M) (Fin M) K} (h : Ji * J = 1) :
    hypJ Ji * hypJ J = 1 := by
  rw [← pm_one]
  simp [hypJ_eq, blk_mul, pm, h]

theorem continuous_pm {X K : Type} [TopologicalSpace X] [CommRing K] [TopologicalSpace K] {M : ℕ} {a b d : X → K}
    {r w : X → Fin M → K} {U : X → Matrix (Fin M) (Fin M) K} (ha : Continuous a) (hb : Continuous b)
    (hr : Continuous r) (hd : Continuous d) (hw : Continuous w) (hU : Continuous U) :
    Continuous fun x => pm (a x) (b x) (r x) (d x) (w x) (U x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  exacts [ha, hb, (continuous_apply j).comp hr, continuous_const, hd, continuous_const, continuous_const,
    (continuous_apply i).comp hw, hU.matrix_elem i j]


end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

-- bundled from Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf ⟨_, hs, S₀, H⟩
  classical
  obtain ⟨S₁, hS₁⟩ := up_fin.1 hc
  have hG' := Filter.eventually_cofinite.1 hG
  obtain ⟨r1, r2, r3, r4, r5, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b n M
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    exact (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)).2.2.2.2.2.2.2.1 n M
  have gd : ∀ v, v ∉ S₁ ∪ hG'.toFinset → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := fun v hv =>
    not_not.1 (mt hG'.mem_toFinset.2 fun h => hv (Finset.mem_union_right _ h))
  have hoff : ∀ v, v ∉ S₁ ∪ hG'.toFinset → m' v (latV b v) = m v (latV b v) := fun v hv => by
    have e1 := congrArg (fun μ => μ (latV b v)) (h2 v)
    simp only [(hS₁ _ Finset.subset_union_left).1 v hv, one_smul, Measure.map_apply (mev v) (r4 v).2.measurableSet] at e1
    rw [← e1]
    exact congrArg _ (Set.ext (gd v hv))
  refine ⟨hf, hs.congr_cofinite ((S₁ ∪ hG'.toFinset).eventually_cofinite_notMem.mono fun v hv => by simp only [hoff v hv]),
    S₀ ∪ (S₁ ∪ hG'.toFinset), fun S hS φi φ hφi hφ => ?_⟩
  have hS' : ∀ v, v ∉ S → v ∉ S₁ ∪ hG'.toFinset := fun v h h' => h (hS (Finset.mem_union_right _ h'))
  obtain ⟨-, u2⟩ := hS₁ S ((Finset.subset_union_left.trans Finset.subset_union_right).trans hS)
  obtain ⟨⟨_, _, _⟩, _, _, _⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have := (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)).2.2.2.2.2.2.2.1 n M
  have hm : Measurable (pureL b S φi φ) := by
    have h3 : Measurable (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
      have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
      have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
      exact Measurable.of_eval fun a => Measurable.of_eval fun i =>
        ((continuous_apply_apply a i).comp r1).measurable
    exact ((hφi.comp h3).mul (Finset.measurable_fun_prod _ fun v _ =>
      (hφ v).comp ((r3 v).comp r2).measurable)).indicator (r5 S).measurableSet
  have e1 : ∀ X, pureL b S φi φ (e X) = pureL b S (fun X => φi (ei X)) (fun v X => φ v (ev v X)) X := fun X => by
    have e2 : e X ∈ intOff b S ↔ X ∈ intOff b S := forall₂_congr fun v hv => by rw [(hpr X).2, gd v (hS' v hv)]
    rw [pureL, pureL]
    by_cases hX : X ∈ intOff b S
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (e2.2 hX)]
      simp only [(hpr X).1, (hpr X).2]
    · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (mt e2.1 hX)]
  rw [lintegral_map hm me]
  simp only [e1]
  rw [H S (Finset.subset_union_left.trans hS) (fun X => φi (ei X)) (fun v X => φ v (ev v X)) (hφi.comp mei)
    fun v => (hφ v).comp (mev v), ← lintegral_map hφi mei, h1,
    Finset.prod_congr rfl fun v _ => (lintegral_map (hφ v) (mev v)).symm,
    tprod_congr fun v : {v // v ∉ S} => congrArg ENNReal.toReal (hoff v.1 (hS' _ v.2)).symm]
  simp only [h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, Finset.prod_mul_distrib]
  rw [mul_mul_mul_comm, ← ENNReal.coe_finsetProd, ← ENNReal.coe_mul, u2, ENNReal.coe_one]
  simp

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

