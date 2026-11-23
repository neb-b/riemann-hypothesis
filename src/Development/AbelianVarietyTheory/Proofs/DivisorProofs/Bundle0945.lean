module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIntersectionEqualsPointsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.ModelRep

section Conj

variable {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mem (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [hG, hg', ← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem conj_mem_inv (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isURepOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hσ
  refine ⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩
  · simpa only [Matrix.mul_one, h1] using ha
  · intro a ha' b hb'
    have e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')
  · have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg

theorem isIrredOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  intro S hS h
  refine hσ S hS fun g hg v hv => ?_
  have := h _ (conj_mem_inv hP hG hg) v hv
  have e : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h1]; simp
  simpa only [e] using this

theorem arr_injective {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  apply Fin.ext
  unfold arr at h'
  split_ifs at h' <;> simp only at h' <;> omega

def arrEquiv {q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_injective hq))

theorem orth_sub (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (f : Fin n → Fin n) :
    ((P⁻¹).submatrix id f)ᴴ * G * (P⁻¹).submatrix id f = (Formalism.REAL.Jm ε).submatrix f f := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [← h3]
  rfl

theorem conj_single (hP : IsUnit P) (e : Fin n ≃ Fin n) (a c : Fin n) :
    (P⁻¹).submatrix id e * Matrix.single a c 1 * ((P⁻¹).submatrix id e)⁻¹ =
      P⁻¹ * Matrix.single (e a) (e c) 1 * P := by
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, h2]
    rfl
  have h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e := by
    ext i j
    simp [Matrix.single_apply]
  rw [h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Conj

theorem model_rep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  intro D V S M τ
  obtain ⟨h1, -, h3, h4, -⟩ := M.ds τ
  refine ⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩
  · obtain ⟨-, p, hp, h⟩ := hs τ
    have := orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))
    refine this.trans ?_
    have hinj := arr_injective (nNeg_le (M.ε τ))
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ hinj]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]
    split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)
  · exact conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c

end GlobalTheory.HolDict.ModelRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsRealIndependent
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddings_real_independent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) (e : Fin k → G.C), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => (fun w i l => G.psi w (e j) i l : InfinitePlace G.F → Fin G.n → Fin G.n → ℂ)) := by
  first | (exact @GlobalTheory.LKCx.psi_linearIndependent_real) | (exact GlobalTheory.LKCx.psi_linearIndependent_real) | (intros; apply GlobalTheory.LKCx.psi_linearIndependent_real  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory

theorem encard_fibre_eq_encard_ringHom : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), IsAffineOpen U →
    IsAffineOpen (π ⁻¹ᵁ U) → ∀ (σ : k →+* ℂ) (y : GlobalTheory.CxPts p σ) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ U),
    (GlobalTheory.Points.PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      {ψ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ | ψ.comp (π.app U).hom = GlobalTheory.CxPts.evHom hy}.encard := by
  intro k _ X Y p q π hπ U hU hV σ y hy
  have hmem : ∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z = y →
      z ∈ CxPts.ptsIn q σ (π ⁻¹ᵁ U) := by
    intro z hz
    have : PtsOver.map π hπ (spMap σ) z ∈ CxPts.ptsIn p σ U := hz ▸ hy
    exact this
  have hcomp : ∀ (z : CxPts q σ) (hz : PtsOver.map π hπ (spMap σ) z = y) (f : Γ(X, U)),
      CxPts.evHom (hmem z hz) ((π.app U).hom f) = CxPts.evHom hy f := by
    intro z hz f
    rw [← CxPts.ev_eq, ← CxPts.ev_eq, CxPts.ev_app π hπ U f z, hz]
  apply Set.encard_congr
  refine Equiv.ofBijective (fun z => ⟨CxPts.evHom (hmem z.1 z.2), RingHom.ext (hcomp z.1 z.2)⟩)
    ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ h
    have h' : CxPts.evHom (hmem z hz) = CxPts.evHom (hmem w hw) := congrArg Subtype.val h
    refine Subtype.ext (Subtype.ext (ext_of_valR hV (hmem z hz) (hmem w hw) fun f => ?_))
    rw [valR_eq _ _ (hmem z hz), valR_eq _ _ (hmem w hw)]
    exact congrArg (fun φ : Γ(Y, π ⁻¹ᵁ U) →+* ℂ => φ f) h'
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ f, ψ ((π.app U).hom f) = CxPts.evHom hy f := fun f => by
      rw [← RingHom.comp_apply, hψ]
    have h₀ : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U) :=
      le_preimage_specMap_fromSpec hV (CommRingCat.ofHom ψ)
    have hv : valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) h₀ =
        CommRingCat.ofHom ψ :=
      valMap_specMap_fromSpec hV (CommRingCat.ofHom ψ) h₀
    have e : (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) ≫ π = y.1 := by
      refine ext_of_valR hU h₀ hy fun f => ?_
      rw [valR_comp, valR_eq _ _ h₀, hv, valR_eq _ _ hy]
      exact hψ' f
    let z : CxPts q σ := ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, by
      rw [← hπ, ← Category.assoc, e, y.2]⟩
    have hz : PtsOver.map π hπ (spMap σ) z = y := Subtype.ext e
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change (valMap (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec) (π ⁻¹ᵁ U) (hmem z hz)).hom = ψ
    rw [hv]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
section
open Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.LowHW

theorem height_root {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * Formalism.REAL.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

theorem height_sum {n : ℕ} (c : Fin n → Fin n → ℕ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) i
      = ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
  simp only [← height_root, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h1 : CDom ε μ Λ) (h2 : CDom ε Λ μ) :
    μ = Λ := by
  obtain ⟨c, hc, e1⟩ := h1
  obtain ⟨d, hd, e2⟩ := h2
  have key : ∀ (c : Fin n → Fin n → ℕ), (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) → ∀ a b : Fin n,
      (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ -(c a b : ℝ) := by
    intro c hc a b
    by_cases h : c a b = 0
    · simp [h]
    · have h3 : (a : ℕ) + 1 ≤ b := (hc a b h).1
      have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h3
      have h5 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hs1 := height_sum c
  have hs2 := height_sum d
  rw [← e1] at hs1
  rw [← e2] at hs2
  have hz : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - μ) i + ∑ i : Fin n, ((i : ℕ) : ℝ) * (μ - Λ) i = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by simp only [Pi.sub_apply]; ring
  have l1 : ∑ a, ∑ b, (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ ∑ a, ∑ b, -(c a b : ℝ) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key c hc a b
  have l2 : ∑ a, ∑ b, (d a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ =>
      (key d hd a b).trans (neg_nonpos.2 (Nat.cast_nonneg _))
  simp only [Finset.sum_neg_distrib] at l1
  have l3 : ∑ a, ∑ b, (c a b : ℝ) ≤ 0 := by linarith
  have hc0 : ∀ a b, (c a b : ℝ) = 0 := by
    intro a b
    refine le_antisymm (le_trans ?_ l3) (Nat.cast_nonneg _)
    calc (c a b : ℝ) ≤ ∑ b, (c a b : ℝ) :=
          Finset.single_le_sum (f := fun b => (c a b : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ b)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, (c a b : ℝ))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ a)
  simp only [hc0, zero_smul, Finset.sum_const_zero] at e1
  exact (sub_eq_zero.1 e1).symm

end GlobalTheory.LowHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCayleyTwoIZpowEqOneForall
section
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem cayley_two_injective :
    Function.Injective (fun x : ℝ => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) := by
  have hne : ∀ x : ℝ, (1 - 2 * Complex.I * x) ≠ 0 := by
    intro x h
    have := congrArg Complex.re h
    simp at this
  intro x y hxy
  simp only at hxy
  rw [div_eq_div_iff (hne x) (hne y)] at hxy
  have h2 : ((x : ℂ) - y) * (4 * Complex.I) = 0 := by linear_combination hxy
  rcases mul_eq_zero.1 h2 with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exfalso; have := Complex.I_ne_zero; apply this; linear_combination h / 4

theorem zpow_cayley_two_eq_one_forall :
    ∀ m : ℤ, (∀ x : ℝ, ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) ^ m = 1) → m = 0 := by
  intro m hm
  by_contra hm0
  set f : ℝ → ℂ := fun x => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x) with hf
  have hn : 0 < m.natAbs := Int.natAbs_pos.2 hm0
  have hpow : ∀ x : ℝ, f x ^ m.natAbs = 1 := by
    intro x
    have h := hm x
    rcases Int.natAbs_eq m with e | e
    · rw [e, zpow_natCast] at h; exact h
    · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h
  let S : Finset ℂ := (Polynomial.nthRoots m.natAbs (1 : ℂ)).toFinset
  have hS : ∀ x : ℝ, f x ∈ S := by
    intro x
    simp only [S, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hn).2 (hpow x)
  have : Finite ℝ :=
    Finite.of_injective (fun x : ℝ => (⟨f x, hS x⟩ : S)) (by
      intro x y hxy
      exact cayley_two_injective (congrArg Subtype.val hxy))
  exact not_finite ℝ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaAtOfIsEtaConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjLocal

section Field

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem val_unif : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) := by
  have h := Formalism.L2.Host.unif_spec P
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h

theorem mk_unit {u : E} (hu : P.valuation E u = 1) : FinitePlace.mk P u = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]
  simp

theorem mk_unif : FinitePlace.mk P ((Formalism.L2.Host.unif P : Eˣ) : E) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp

end Field

variable {D : D7}

noncomputable def locHom {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ where
  toFun := locU he
  map_one' := Units.ext (by rw [locU_val]; simp [locE])
  map_mul' k l := Units.ext (by rw [Units.val_mul, locU_val, locU_val, locU_val, locE_mul_locE he, Units.val_mul])

theorem locE_parts {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (u : D.host.E)
    (hu : P.valuation D.host.E u ≤ 1) : infPart D (locE D e u) = 1 ∧ finPart D (locE D e u) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩
  rw [hint]
  intro Q
  have h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u := hι u
  have h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1) :=
    GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5, h4]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu
  · rw [h3 Q hQ]
    simp

end GlobalTheory.EtaConjLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStarStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_adic_integral_span_closed_mul_star : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_mul_star_eventually) | (exact GlobalTheory.AdicSpan.isIntB_mul_star_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_mul_star_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), piV G v '' Ω ⊆ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.cptInt) | (exact GlobalTheory.OrbFinAf.cptInt) | (intros; apply GlobalTheory.OrbFinAf.cptInt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRingStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_tensor_points_sharp_stable_ring : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  first | (exact @GlobalTheory.OrbFinAf.intV_order_eventually) | (exact GlobalTheory.OrbFinAf.intV_order_eventually) | (intros; apply GlobalTheory.OrbFinAf.intV_order_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v := by
  first | (exact @GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (exact GlobalTheory.OrbFinAf.mul_mem_IntV_eventually) | (intros; apply GlobalTheory.OrbFinAf.mul_mem_IntV_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExpStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (exact GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (intros; apply GlobalTheory.OrbFinAf.isIntV_mul_eventually' <;> assumption)
end

