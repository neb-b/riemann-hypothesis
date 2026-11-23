module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearGKMapExtendsToSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinprodFiniteHeightTransposeGramUnitaryLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

def cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : NNReal :=
  max 1 (Finset.univ.sup fun k : Fin (Module.finrank D.host.F D.host.E) =>
    absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)))

theorem one_le_cst (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : 1 ≤ cst D v := le_max_left _ _

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    simp only [compFin, evFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.comp_apply, AlgHom.id_apply]

theorem sum_finCoord (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) = y := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (Module.finBasis D.host.F D.host.E)).sum_repr y]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem absFin_map_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) y) ≤
      cst D v * Finset.univ.sup fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊ := by
  conv_lhs => rw [← sum_finCoord y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine absFin_sum_le _ v _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e1 : evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) =
      (evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k) ⊗ₜ[D.host.F] (1 : D.host.E)) *
        ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e1]
  refine (absFin_mul_le _ v _ _).trans ?_
  rw [absFin_tmul_one, mul_comm]
  refine mul_le_mul' ?_ ?_
  · exact le_max_of_le_right (Finset.le_sup (f := fun k : Fin (Module.finrank D.host.F D.host.E) =>
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))) (Finset.mem_univ k))
  · exact Finset.le_sup (f := fun k => ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D y k)‖₊) (Finset.mem_univ k)

theorem absFin_le (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    absFin D.host.F v (compFin D.host.F D.host.E v y) ≤ cst D v * Finset.univ.sup fun k =>
      ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) k)‖₊ := by
  rw [compFin_eq]
  exact absFin_map_le v _

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree.FinHeightBound

open GlobalTheory.AdelicU

variable {D : D7}

theorem coordNorm_le_finNorm (X : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D X) (a b : Fin X.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) :
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h a b) k)‖₊ ≤
      GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  have := Finset.le_sup (f := fun p : Fin X.rank × Fin X.rank × Fin (Module.finrank D.host.F D.host.E) =>
    ‖evalV D.host.F v (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (finMat D.sp.cm.sig X.gram h p.1 p.2.1) p.2.2)‖₊)
    (Finset.mem_univ (a, b, k))
  dsimp only at this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm
  exact this

theorem normFin_reindex_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : GA D X) :
    normFin D.host.F v ((reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v)) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finNorm X v h := by
  refine (normFin_le_iff D.host.F v).2 fun i j => ?_
  rw [Matrix.map_apply, reindex_apply, Matrix.submatrix_apply]
  have hfm : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j)) = finMat D.sp.cm.sig X.gram h (e.symm i) (e.symm j) := rfl
  have h1 := absFin_le v (Formalism.L2.Theta.mt X h (e.symm i) (e.symm j))
  rw [hfm] at h1
  have h2 := Finset.sup_le (s := Finset.univ) fun k _ => coordNorm_le_finNorm X v h (e.symm i) (e.symm j) k
  exact h1.trans (mul_le_mul' le_rfl h2)

theorem kapX_inv (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) : (kapX X e hJ h).1⁻¹ = (kapX X e hJ h⁻¹).1 := by
  show (Units.map _ (Formalism.L2.Theta.matHom X h))⁻¹ = Units.map _ (Formalism.L2.Theta.matHom X h⁻¹)
  rw [map_inv, map_inv]

theorem coe_bc_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ((Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1 : GL (Fin d) _) : Matrix (Fin d) (Fin d) _) =
      (reindex e e (Formalism.L2.Theta.mt X h)).map (compFin D.host.F D.host.E v) := by
  rw [← mat_kapX X e hJ h]
  rfl

theorem htFin_kapX_le (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (h : GA D X) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      cst D v * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  have h1 := normFin_reindex_le X e v h
  have h2 := normFin_reindex_le X e v h⁻¹
  unfold htFin htOf GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt
  rw [← map_inv, kapX_inv, coe_bc_kapX, coe_bc_kapX]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (one_le_cst D v).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · exact h1.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_left _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (le_max_of_le_right (le_max_right _ _)))

theorem cst_mulSupport_finite (D : D7) : Function.HasFiniteMulSupport (cst D) := by
  have h : ∀ k : Fin (Module.finrank D.host.F D.host.E), ∀ᶠ v in Filter.cofinite,
      absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) ≤ 1 := by
    intro k
    refine (eventually_absFin_le_one D.host.F
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k))).mono fun v hv => ?_
    have e1 : compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k)) =
        (1 : Fv D.host.F v) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
      simp only [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply]
    rwa [e1] at hv
  refine (Filter.eventually_cofinite.1 (Filter.eventually_all.2 h)).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun k _ => hv' k)

end GlobalTheory.SquareAgree.FinHeightBound

namespace GlobalTheory.SquareAgree

open GlobalTheory.AdelicU GlobalTheory.SquareAgree.FinHeightBound

theorem finprod_htFin_kapX_le : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal,
    ∀ h : GA D X, ∏ᶠ v, GlobalTheory.AdelicU.htFin D.host.F v
      (Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (kapX X e hJ h).1) ≤
      C * ∏ᶠ v, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h := by
  intro D X d e J hJ
  refine ⟨∏ᶠ v, cst D v, fun h => ?_⟩
  have hc := cst_mulSupport_finite D
  have hf : Function.HasFiniteMulSupport fun v => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt X v h :=
    GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finHt_mulSupport_finite X h
  rw [← finprod_mul_distrib hc hf]
  refine finprod_le_finprod₀ (finite_mulSupport_htFin D.host.F (kapX X e hJ h).1) (fun _ => bot_le) ?_
    (fun v => htFin_kapX_le X e hJ h v)
  exact (hc.union hf).subset (Function.mulSupport_mul _ _)

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExt

theorem kset_sub {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ Formalism.MainNotions.S.UJset ε := by
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  rw [Matrix.star_eq_conjTranspose] at h1
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem conj_back {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem exp_conj_inv {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_UH {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  change (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) * g) * P := by
        rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk, h]

theorem extExists : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7,
    GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.ExtExists D := by
  intro hHC hCW D θ hθ V S M J χ μ 𝓕 _ _ T₀ hT₀
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨U, N, hU, hTU⟩ := _root_.GlobalTheory.GKUnif.exists_level_exponent hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
    obtain ⟨E, i1, i2, i3, i4, i5, i6, p, ι, hinj, hrange, hp, hπ⟩ :=
      GlobalTheory.T.exists_smoothCuspForm_frechet_moderateGrowth_rep D θ hθ V (GlobalTheory.ChainFr.Fr.ofModel M) U N hU
    choose π dπ hπ using hπ
    have hmem : ∀ u, T₀ u ∈ LinearMap.range ι := fun u => by
      have ha := hT₀.1 u
      obtain ⟨x, hx⟩ := (hrange _).2 ⟨ha.cont, ha.left, (hTU u).1, hT₀.2.1 u, hT₀.2.2.1 u, (hTU u).2⟩
      exact ⟨x, hx⟩
    let e := LinearEquiv.ofInjective ι hinj
    let T₀' : (Π τ : D.what₂.Tau, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →ₘₗ[ℂ] E :=
      e.symm.toLinearMap.compMultilinearMap (T₀.codRestrict (LinearMap.range ι) hmem)
    have hT₀' : ∀ u, ι (T₀' u) = T₀ u := fun u => by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨T₀ u, hmem u⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    have hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ),
        (w : M.H τ) = M.σ τ k (u τ) → T₀' (Function.update u τ w) = π τ k (T₀' u) := by
      intro τ k hk u w hw
      apply hinj
      rw [(hπ τ).2.1 k (kset_sub hk), hT₀', hT₀']
      have hk' : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := conj_back (M.fr_unit τ)
      have hmax : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
        change M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
        rw [hk']; exact hk
      refine (hT₀.2.2.2.2.2.2.1 τ _ hmax u w ?_).trans rfl
      rw [hw]
      show _ = M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹) _
      rw [hk']
    have hL : ∀ τ, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ), ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M)
        (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), (w : M.H τ) = dRep (M.σ τ) X (u τ) →
        T₀' (Function.update u τ w) = dπ τ X (T₀' u) := by
      intro τ X hX u w hw
      apply hinj
      rw [(hπ τ).2.2 X hX, hT₀', hT₀']
      have hd : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) = dRep (M.σ τ) X := by
        funext y
        unfold dRep
        congr 1
        funext t
        show M.σ τ (M.fr τ * NormedSpace.exp (t • ((M.fr τ)⁻¹ * X * M.fr τ)) * (M.fr τ)⁻¹) y = _
        rw [exp_conj_inv (M.fr_unit τ), conj_back (M.fr_unit τ)]
      exact hT₀.2.2.2.2.2.2.2 τ _ (conj_mem_lieAt M τ hX) u w (by rw [hw, hd])
    have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ g' ∈ Formalism.MainNotions.S.UJset (M.ε τ'),
        (π τ g).comp (π τ' g') = (π τ' g').comp (π τ g) := by
      intro τ τ' hne g hg g' hg'
      ext x
      apply hinj
      simp only [ContinuousLinearMap.comp_apply]
      rw [(hπ τ).2.1 g hg, (hπ τ').2.1 g' hg', (hπ τ').2.1 g' hg', (hπ τ).2.1 g hg]
      funext y
      simp only [rTr, mul_assoc]
      exact congrArg (fun z => ι x (y * z)) (_root_.GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) _
        (conj_mem_UH (M.fr_unit τ') (M.fr_gram τ') hg'))
    obtain ⟨TE, hTE1, hTE2, hTE3⟩ := _root_.GlobalTheory.FactorExtension.extend_positions hHC hCW D V S M E p π dπ (fun τ => (hπ τ).1) hcomm T₀' hK hL
    obtain ⟨hequiv, hcont⟩ := GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous D θ V S M E p ι N π hp
      (fun x d => ((hrange (ι x)).1 ⟨x, rfl⟩).2.2.2.2.2 d) (fun τ => (hπ τ).2.1) TE hTE2 hTE3
    let T : MMap M := ι.compMultilinearMap TE
    have hext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ := fun v u h => by
      show ι (TE v) = T₀ u
      rw [hTE1 v u h, hT₀']
    refine ⟨T, ⟨?_, fun v => ((hrange _).1 ⟨TE v, rfl⟩).2.2.2.2.1,
      _root_.GlobalTheory.GKExtLevel.lev hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont, hequiv, hcont⟩, hext⟩
    exact _root_.GlobalTheory.EquivValues.isAutFunSm hHC D θ hθ V S M T U N hU (fun v => by
      have h := (hrange (ι (TE v))).1 ⟨TE v, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩) hequiv hcont
  · rintro T T' ⟨hT, hTe⟩ ⟨hT', hT'e⟩
    have hd : T - T' ∈ Mult θ M J χ := Submodule.sub_mem _ (Submodule.subset_span hT) (Submodule.subset_span hT')
    refine sub_eq_zero.1 (GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M J χ (T - T') hd fun v hv => ?_)
    rw [MultilinearMap.sub_apply, hTe v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl),
      hT'e v (fun τ => ⟨v τ, hv τ⟩) (fun τ => rfl), sub_self]

end GlobalTheory.GKExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareComm.AlgDeriv

open Complex GlobalTheory.FockIndep GlobalTheory.ArchRec.DerFock
open scoped Real

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem exists_dRho_pure_all (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS frS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (εS : D.what₂.Tau → Fin S.rank → Bool)
    (sT frT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (εT : D.what₂.Tau → Fin T.rank → Bool)
    (hfS : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D S ρ) (sS ρ) (εS ρ) (frS ρ))
    (hfT : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D T ρ) (sT ρ) (εT ρ) (frT ρ))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ L : Module.End ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ), ∀ f, IsThetaFunO ψ S T f →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → ∀ P,
      Datum.dRho (heisO ψ S T) θ τ z (pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f P) =
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f (L P) := by
  classical
  have hS := fun ρ => isCartanInv_of_isFrameOf (hfS ρ)
  have hT := fun ρ => isCartanInv_of_isFrameOf (hfT ρ)
  let A : FVar D T.rank S.rank → (WO S T → ℂ) → (WO S T → ℂ) :=
    aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ)) (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)
  let u : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun k => unitMap (frS τ)⁻¹ (frT τ)⁻¹ k.1 k.2
  let α : Fin T.rank × Fin S.rank → ℂ := fun k =>
    if (εT τ k.1 == εS τ k.2) then (frT τ * z * (frS τ)⁻¹) k.1 k.2
    else starRingEnd ℂ ((frT τ * z * (frS τ)⁻¹) k.1 k.2)
  let c : FVar D T.rank S.rank → ℂ := fun k => if k.1 = τ then (fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) *
    ((omDir S T τ z τ (u k.2) : ℝ) + I * (omDir S T τ (cplxO (sS τ) (sT τ) z) τ (u k.2) : ℝ))) else 0
  refine ⟨(1 / 2 : ℂ) • ((∑ k, c k • (MvPolynomial.pderiv k).toLinearMap) +
    (fockScale D τ : ℂ) • ∑ k : Fin T.rank × Fin S.rank,
      α k • LinearMap.mulLeft ℂ (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank))), fun f hf hv P => ?_⟩
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A k g) := fun k _ h => aPlus_theta hψ hθ k.1 _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g) := by
    rintro ⟨ρ, a, b⟩ ⟨ρ', a', b'⟩ g h
    by_cases e : ρ = ρ'
    · subst e
      exact aPlus_comm (hS ρ) (hT ρ) _ _ hψ hθ h
    · exact GlobalTheory.TwoPlaceComm.aPlus_comm_ne hψ hθ e _ _ _ _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hm := pure_mem hadd hsm hA hf P
  have hBA : ∀ j g, IsThetaFunO ψ S T g → Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (A j g) =
      A j (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) + c j • g := by
    rintro ⟨ρ, a, b⟩ g h
    by_cases e : ρ = τ
    · subst e
      refine (annih_aPlus (hS ρ) (hT ρ) z (u (a, b)) hψ hθ h).trans ?_
      congr 2
      exact (if_pos rfl).symm
    · rw [show c (ρ, a, b) = 0 from if_neg e, zero_smul, add_zero]
      exact GlobalTheory.TwoPlaceComm.annih_aPlus_ne hψ hθ (Ne.symm e) _ _ _ _ h
  have h1 := pure_deriv (B := Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z) (c := c) hadd hsm hA hc Aadd Asm
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h) hBA hf (hv z) P
  have h2 : Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (pureTensorL A f P) =
      pureTensorL A f (∑ k : Fin T.rank × Fin S.rank,
        α k • (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank) * P)) := by
    conv_lhs => rw [eq_sum_unitMap (hfS τ).1 (hfT τ).1 z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hm _ _ (cplxO_unitMap (hfS τ) (hfT τ) k.1 k.2), map_smul,
      pure_X_mul hadd hsm hA hc Aadd Asm hf]
    rfl
  have h3 : ∀ g, Datum.dRho (heisO ψ S T) θ τ z g =
      (1 / 2 : ℂ) • (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g +
        (fockScale D τ : ℂ) • Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) := fun g => by
    rw [Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero τ), one_smul, Datum.annih, Datum.crea]
    module
  change Datum.dRho (heisO ψ S T) θ τ z (pureTensorL A f P) = pureTensorL A f _
  rw [h3, h1, h2, ← map_smul, ← map_add (f := _), ← map_smul]
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
  rfl

end GlobalTheory.SquareComm.AlgDeriv


open GlobalTheory.SquareComm.AlgDeriv in
theorem GlobalTheory.SquareComm.dRho_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε S X A B f hf τ z
  have hth : ∀ g ∈ algF ψ θ ε A B, IsThetaFunO ψ (sgn ε S) X g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, P, hf₀, rfl⟩ := hx
      exact GlobalTheory.FockIndep.pure_mem (A := aPlusAll (heisO ψ (sgn ε S) X) θ
          (fun ρ => cplxO ((frSgn ε A).cart ρ) (B.cart ρ)) A.onb B.onb) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun k _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 _ _ h) hf₀.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul a x _ hx => exact GlobalTheory.OrientedHeis.theta_smul a hx
  obtain ⟨L, hL⟩ := exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart (frSgn ε A).fr (frSgn ε A).ε
    B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
    (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ z
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hf₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨f₀, L P, hf₀, hL f₀ hf₀.1 (hf₀.2 τ) P⟩
  | zero =>
    have h0 := GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε S) (T := X))
    rw [zero_smul, zero_smul] at h0
    rw [h0]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [GlobalTheory.FockIndep.dRho_add (S := sgn ε S) (T := X) hψ hθ τ z (hth x hx) (hth y hy)]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z a (hth x hx)]
    exact Submodule.smul_mem _ a ih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piInf)

namespace GlobalTheory.VacDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def IsGaussEq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    ∀ x, deriv (fun t : ℝ => M.heisLine ψ u' t Φ x) 0 = Complex.I * deriv (fun t : ℝ => M.heisLine ψ u t Φ x) 0

end GlobalTheory.VacDatum

end
end

