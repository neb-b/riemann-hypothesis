module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothKFiniteCenter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGL
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

section Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

def skewGram (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) : GL (Fin m) (Fv F v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (J.map τ) (by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero τ).2 hd)

theorem map_comp_conj_skew (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v) :
    J.map (τ.comp σ) = -(J.map τ)ᵀ :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, AlgHom.comp_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [hs j i, map_neg]

theorem splitPairMat_unitary_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v)
    {a b : Matrix (Fin m) (Fin m) (Fv F v)} (e : bᵀ * J.map τ * a = J.map τ) :
    Formalism.UG.cT (sigR _ σ) (splitPairMat h τ a b) * JR (Fv F v) J * splitPairMat h τ a b = JR (Fv F v) J := by
  refine splitMat_ext h τ ?_ ?_
  · rw [map_unitary, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, e]
  · rw [map_unitary, comp_conj_conj h, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj,
      map_comp_conj_skew hs, Matrix.mul_neg, Matrix.neg_mul, neg_inj,
      ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, e]

theorem splitHom_injective_skew (h : IsCMExt F E σ) (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) :
    Function.Injective (splitHom σ J τ) := fun g g' e => by
  have c : ∀ x : GLoc σ J v, splitHom σ J (τ.comp σ) x = dualConj (skewGram hd τ) (splitHom σ J τ x) :=
    fun x => eq_dualConj_iff.2 (splitHom_unitary τ x)
  exact matHom_injective _ σ J (Units.ext (splitMat_ext h τ (congrArg Units.val e) (by
    rw [← splitHom_val, ← splitHom_val, c, c, e])))

theorem splitHom_surjective_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) : Function.Surjective (splitHom σ J τ) := fun x =>
  ⟨(⟨splitPairGL h τ x (dualConj (skewGram hd τ) x),
    splitPairMat_unitary_skew h hs τ ((eq_dualConj_iff (A := skewGram hd τ)).1 rfl)⟩ : HR (Fv F v) σ J),
    Units.ext (splitPairMat_map h τ _ _)⟩

end Skew

theorem blkGL_bijective {R : Type} [CommRing R] (n : ℕ) : Function.Bijective (blkGL (R := R) n) :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv).bijective

theorem Jst_mul_self (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  have e : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) *
      Matrix.fromBlocks 0 1 (-1) 0 = -1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have e2 := Matrix.submatrix_mul_equiv
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (finSumFinEquiv (m := n) (n := n)).symm (finSumFinEquiv (m := n) (n := n)).symm
    (finSumFinEquiv (m := n) (n := n)).symm
  rw [e] at e2
  refine e2.trans (Matrix.ext fun i j => ?_)
  simp [Matrix.one_apply]

theorem Jst_det_ne_zero (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  have : IsUnit (Jst D n).det :=
    Matrix.isUnit_det_of_left_inverse (B := -Jst D n) (by rw [Matrix.neg_mul, Jst_mul_self, neg_neg])
  exact this.ne_zero

theorem Jst_skew (D : D7) (n : ℕ) (i j : Fin (n + n)) :
    D.sp.cm.sig (Jst D n j i) = -Jst D n i j := by
  have key : ∀ a b : Fin n ⊕ Fin n,
      D.sp.cm.sig ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) b a) =
        -(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) a b := by
    rintro (a | a) (b | b) <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, neg_zero, map_neg]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
  exact key _ _

theorem thU_bijective : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    Function.Bijective (thU D n v τ) := fun D n _ τ =>
  (blkGL_bijective n).comp
    ⟨splitHom_injective_skew (isCMExt_host D) (Jst_det_ne_zero D n) τ,
      splitHom_surjective_skew (isCMExt_host D) (Jst_skew D n) (Jst_det_ne_zero D n) τ⟩

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCoefficientEquivariance
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcShift


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem zc_shift : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  intro D n ρ p hn M m ψ hψ b₀ F hF c h
  obtain ⟨hadd, hnorm, hrat, -⟩ := _root_.GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  obtain ⟨hl, hFD, -⟩ := m.hz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := countable_of_Lindelof_of_discrete
  have hnz : ∀ z z' : hermA D ρ, M.nzx z 0 * M.nzx z' 0 = M.nzx (z + z') 0 := fun z z' => by
    have := _root_.GlobalTheory.CompanionTheory.NzxAdd.nzx_add M z z' 0 0
    rwa [add_zero] at this
  have hconj : conj (chz ψ b₀ c) * chz ψ b₀ c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  set u : hermA D ρ → ℂ := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) with hu
  have hper : ∀ γ ∈ ratHerm D ρ, ∀ x, u (γ + x) = u x := by
    intro γ hγ x
    simp only [hu]
    rw [← hnz, mul_assoc, hF _ ((_root_.GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF M).2.2 γ hγ), hadd, hrat γ hγ, one_mul]
  have hpt : ∀ z : hermA D ρ, F (M.nzx z 0 * (M.nzx c 0 * h)) * conj (chz ψ b₀ z) = chz ψ b₀ c * u (z + c) := by
    intro z
    simp only [hu]
    rw [← mul_assoc, hnz, hadd, map_mul]
    linear_combination (-(F (M.nzx (z + c) 0 * h) * conj (chz ψ b₀ z))) * hconj
  unfold zc
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  exact GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D ρ) m.lz hFD u hper c

end GlobalTheory.CompanionTheory.ZcShift

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPartialFourierMeanStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), Continuous Φ → IsPer Φ → Continuous (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.continuous_pm | exact GlobalTheory.CompanionTheory.PcFc.continuous_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.continuous_pm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFiniteVectorsHolds
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFinite

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem mem_of_stable {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) (W : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable W) (h0 : W ≠ ⊥)
    (hW : ∀ φ ∈ W, IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) (φ : Sm E a)
    (hφ : IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) : φ ∈ W :=
  _root_.GlobalTheory.CompanionTheory.CuspIrred.irred_module E a μ H hH hi W hs h0 hW φ hφ

theorem exists_cusp_form_of_K_finite {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) {F : L2 (latticeGL E a) μ} (hF : F ∈ H) (hk : IsKFinL2 μ F) :
    ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H := by
  obtain ⟨φ, e, hm, hl, hz, hlev, hkf, hzf⟩ := _root_.GlobalTheory.CompanionTheory.SmoothRep.smoothRep E a μ H hH hi F hF hk
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hlev
  have hFe : hm.toL2 = F := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans e.symm)
  have hcusp : IsCuspidal φ.1 := _root_.GlobalTheory.CompanionTheory.CuspL2.isCuspidal_of_toL2_mem E a μ φ.1 hc hl hz hm (by rw [hFe]; exact hH hF)
  exact ⟨φ, e, ⟨⟨hl, hlev, hkf, hzf, _root_.GlobalTheory.CompanionTheory.Growth.moderate_growth E a μ φ hl hz hlev hkf hzf hm⟩, hcusp⟩, hz, hm,
    by rw [hFe]; exact hF⟩

end GlobalTheory.CompanionTheory.CuspFinite

namespace GlobalTheory.CompanionTheory.Published


open GlobalTheory.CompanionTheory.CuspFinite in
theorem cuspFiniteVectorsGL : GlobalTheory.Published.CuspFiniteVectorsGL := by
  intro E _ _ _ a μ _ _ H hH hi
  obtain ⟨V, hV, hs⟩ := GlobalTheory.T.irreducible_cuspidal_smooth_module E a μ H hH hi
  have hkf : ∀ F ∈ H, IsKFinL2 μ F → F ∈ classes V μ := fun F hF hk => by
    obtain ⟨φ, e, h1, h2, h3⟩ := exists_cusp_form_of_K_finite hH hi hF hk
    exact ⟨φ, (hV φ).2 ⟨h1, h2, h3⟩, e⟩
  have hcl : classes V μ ≤ H := by
    rintro F ⟨φ, hφ, e⟩
    obtain ⟨-, -, h, hH'⟩ := (hV φ).1 hφ
    have : F = h.toL2 := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans h.lift_toL2_ae_eq.symm)
    exact this ▸ hH'
  have hdense : H ≤ (classes V μ).topologicalClosure :=
    (GlobalTheory.T.K_finite_vectors_dense E a μ H hi.1).trans (Submodule.topologicalClosure_mono
      (Submodule.span_le.2 fun F hF => hkf F hF.1 hF.2))
  have hne : V ≠ ⊥ := by
    intro hb
    refine hi.2.1 (eq_bot_iff.2 (hdense.trans (Submodule.topologicalClosure_minimal _ ?_ ?_)))
    · rintro F ⟨φ, hφ, e⟩
      rw [hb, Submodule.mem_bot] at hφ
      have h0 : φ.1 = 0 := by rw [hφ]; rfl
      rw [h0] at e
      exact (Submodule.mem_bot ℂ).2 (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (e.trans (show lift (latticeGL E a) (0 : L2 (latticeGL E a) μ) =ᵐ[μ] 0 from
        ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)).symm))
    · rw [Submodule.bot_coe]
      exact isClosed_singleton
  have hirr : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V := fun W hWV hWs => by
    by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (le_antisymm hWV fun φ hφ =>
        mem_of_stable hH hi W hWs h0 (fun ψ hψ => (hV ψ).1 (hWV hψ)) φ ((hV φ).1 hφ))
  let π : CuspSub E a := ⟨V, fun φ hφ => ((hV φ).1 hφ).1, hs, hne, hirr⟩
  exact ⟨π, fun φ hφ => ((hV φ).1 hφ).2.1, fun φ hφ => ((hV φ).1 hφ).2.2.1,
    le_antisymm (Submodule.topologicalClosure_minimal _ hcl hi.1.1) hdense, hkf⟩

end GlobalTheory.CompanionTheory.Published

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenOfRightInvariant
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.B3

variable {D : D7} {n : ℕ} {v : Pl D}

theorem term_eq {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ) {z : ℂ}
    {f : G D n → ℂ} (hf : IsLaw χ z f) (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (C : Cut D n v) (g : G D n) (p₀ : PV D n v) {k₀ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀)
    {k : G D n} (hk : k ∈ KAt D n v) {x : hermA D n} (hx : x ∈ C.s) :
    f (g * (k * nb x)) = sphV D n v z (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x)) * f g := by
  obtain ⟨p₁, k₁, hk₁, e₁⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x))
  have hu : k * nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem hk.2 (nb_mem_atPts hnb C hx)
  rw [shift hf hK g p₀ p₁ hk₀ hk₁ e₀ hu e₁, lawV, chi_one hχ hnb hk₀ hk₁ hk x p₁ e₁, e₁, Circle.coe_one, one_mul]
  congr 1
  exact (congrArg (fun r => npow r (z + (n : ℂ) / 2))
    (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) p₁ hk₁)).symm

theorem eigen_of_rightInvariant : SectionEigenfunctionMaximalCompact := by
  intro D n χ nb hnb v τ hχ C νv hν z c hc f hf hK g
  obtain ⟨p₀, k₀, hk₀, e₀⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (proj D.sp.cm.sig (Jst D n) v g)
  have hκ : emb D.sp.cm.sig (Jst D n) v k₀ ∈ KAt D n v :=
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk₀, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  have key : ∀ k : KAt D n v, cutR nb C f (g * k) =
      f g * (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)))
        (⟨_, hκ⟩ * k) := by
    intro k
    simp only [PositivityTheory.Rg.Rsw.L.cutR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc g, term_eq hχ hf hK hnb C g p₀ hk₀ e₀ k.2 hx]
    have e : proj D.sp.cm.sig (Jst D n) v ((((⟨_, hκ⟩ : KAt D n v) * k : KAt D n v) : G D n) * nb x) =
        k₀ * proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x) := by
      rw [Subgroup.coe_mul, mul_assoc, map_mul, proj_emb_self]
    rw [e]
    ring
  simp only [key]
  rw [integral_const_mul, integral_mul_left_eq_self
    (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x))) ⟨_, hκ⟩,
    hc, mul_comm]

end GlobalTheory.CompanionTheory.Jp.B3

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsResidueCharacterOfConductor
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.ResChar

theorem local_component_additive_character_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have h1 : singleV F v (r + s) = singleV F v r + singleV F v s := by
    classical
    unfold singleV
    first
    | exact Subtype.ext (Pi.single_add v r s)
    | (apply Subtype.ext
       exact Pi.single_add v r s)
    | (apply Subtype.ext
       funext w
       show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
       rw [Pi.single_add]
       rfl)
  have h2 : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [h1]
    show ((0 : Ainf F), singleV F v r + singleV F v s) = ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  simp only [psiV]
  rw [h2, AddChar.map_add_eq_mul]

theorem dvd_of_nonunit {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] {p x : R}
    (hp : Irreducible p) (hx : ¬ IsUnit x) : p ∣ x := by
  rcases ValuationRing.dvd_total p x with h | ⟨c, hc⟩
  · exact h
  · rcases hp.isUnit_or_isUnit hc with h | h
    · exact absurd h hx
    · exact ⟨↑h.unit⁻¹, by rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ ϖ : Ov D v, Irreducible ϖ → ∀ w : (Lv D v)ˣ, (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → ∃ ψ₀ : AddChar (kv D v) ℂ, ψ₀ ≠ 1 ∧ ∀ c : Ov D v, psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) = ψ₀ (IsLocalRing.residue (Ov D v) c) := by
  intro D ψ v hψ ϖ hϖ w hw
  classical
  set f : Ov D v → ℂ := fun c => psiV D.host.F ψ v (((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) c) with hf
  have hadd : ∀ a b, f (a + b) = f a * f b := by
    intro a b
    simp only [hf, map_add (f := _), mul_add]
    exact local_component_additive_character_add ψ v _ _
  have hker : ∀ d, f (ϖ * d) = 1 := by
    intro d
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) (ϖ * d) = algebraMap (Ov D v) (Lv D v) d := by
      rw [map_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    simp only [hf, e]
    exact hψ.1 _ d.2
  have hwd : ∀ a b, IsLocalRing.residue (Ov D v) a = IsLocalRing.residue (Ov D v) b → f a = f b := by
    intro a b h
    have h0 : IsLocalRing.residue (Ov D v) (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨d, hd⟩ := dvd_of_nonunit hϖ (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
    have e : a = b + ϖ * d := by rw [← hd]; ring
    rw [e, hadd, hker, mul_one]
  have hf0 : f 0 = 1 := by simpa using hker 0
  let g : kv D v → Ov D v := fun z => Classical.choose (IsLocalRing.residue_surjective z)
  have hg : ∀ z, IsLocalRing.residue (Ov D v) (g z) = z := fun z =>
    Classical.choose_spec (IsLocalRing.residue_surjective z)
  let ψ₀ : AddChar (kv D v) ℂ :=
    { toFun := fun z => f (g z)
      map_zero_eq_one' := by
        show f (g 0) = 1
        rw [hwd (g 0) 0 (by rw [hg, map_zero]), hf0]
      map_add_eq_mul' := by
        intro z z'
        show f (g (z + z')) = f (g z) * f (g z')
        rw [← hadd]
        exact hwd _ _ (by rw [hg, map_add (f := _), hg, hg]) }
  have hψ₀ : ∀ c, ψ₀ (IsLocalRing.residue (Ov D v) c) = f c := fun c => by
    show f (g _) = f c
    exact hwd _ _ (hg _)
  refine ⟨ψ₀, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
    intro h1
    apply hb
    have e1 : ψ₀ (IsLocalRing.residue (Ov D v) b) = 1 := by rw [h1]; exact AddChar.one_apply _
    rw [hψ₀] at e1
    have e : ((w⁻¹ : (Lv D v)ˣ) : Lv D v) * algebraMap (Ov D v) (Lv D v) b = (b : Fv D.host.F v) / (ϖ : Fv D.host.F v) := by
      rw [Units.val_inv_eq_inv_val, hw, div_eq_inv_mul]; rfl
    rw [← e]
    exact e1
  · intro c
    exact (hψ₀ c).symm

end GlobalTheory.CompanionTheory.Jp.ResChar

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugationStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_conjugation : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 → ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.fc_levi | exact GlobalTheory.CompanionTheory.PcFc.fc_levi | (intros; apply GlobalTheory.CompanionTheory.PcFc.fc_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerateStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
  ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
  ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | exact GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | (intros; apply GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalFormStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_diagonal_normal_form : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n), ρ ≤ β.1.rank → ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | exact GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | (intros; apply GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum <;> assumption)
end

