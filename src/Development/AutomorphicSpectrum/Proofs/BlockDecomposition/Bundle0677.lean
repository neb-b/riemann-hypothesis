module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetUpperTriangularBlock
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

theorem det_upper_triangular_block {A : Type} [CommRing A] {n : ℕ} (a b d : Matrix (Fin n) (Fin n) A) : (blk4 a b 0 d).det = a.det * d.det := by
  rw [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_cT {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    (Formalism.UG.cT s M).det = s M.det := by
  rw [Formalism.UG.cT, Matrix.det_transpose]
  exact (RingHom.map_det s M).symm

theorem exists_det_parabolic {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = blk4 0 1 (-1) 0)
    (p : GlobalTheory.LocIntw.upperParabolic R σ Q) : ∃ d : R ⊗[F] E,
      (GlobalTheory.LocIntw.matR R σ p.1).det = (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d ∧
      sigR R σ (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) * d = 1 := by
  obtain ⟨a, b, c, d, e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR R σ p.1)
  obtain rfl : c = 0 := Matrix.ext fun i j => by
    have := GlobalTheory.LocIntw.lower_eq_zero p.2 i j
    rwa [e, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  have hu : Formalism.UG.cT (sigR R σ) (GlobalTheory.LocIntw.matR R σ p.1) * JR R Q * GlobalTheory.LocIntw.matR R σ p.1 = JR R Q := p.1.2
  rw [GlobalTheory.LocIntw.JR_eq R hQ, e, GlobalTheory.LocIntw.cT_blk4, GlobalTheory.LocIntw.cT_zero', StdUnn.Model.submatrix_fromBlocks_mul,
    StdUnn.Model.submatrix_fromBlocks_mul] at hu
  have hd : Formalism.UG.cT (sigR R σ) a * d = 1 := by simpa using (StdUnn.Model.blockMatrixTwoByTwoFin_injective hu).2.1
  have ha : (GlobalTheory.LocIntw.aUp R σ Q p : R ⊗[F] E) = a.det := by
    rw [GlobalTheory.LocIntw.coe_aUp, e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  refine ⟨d.det, ?_, ?_⟩
  · rw [ha, e, det_upper_triangular_block]
  · have h5 : (Formalism.UG.cT (sigR R σ) a * d).det = 1 := by rw [hd, Matrix.det_one]
    rw [Matrix.det_mul, det_cT] at h5
    rw [ha]
    exact h5

theorem eq_of_mul_eq_one {a b c : ℝ} (h1 : a * c = 1) (h2 : b * c = 1) : a = b := by
  have hc : c ≠ 0 := right_ne_zero_of_mul_eq_one h1
  exact mul_right_cancel₀ hc (h1.trans h2.symm)

abbrev PV (D : D7) (n : ℕ) (v : Pl D) : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) :=
  GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n)

abbrev aV (p : PV D n v) : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ :=
  GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) p

def lawV (χ : (AE D)ˣ →* Circle) (z : ℂ) (p : PV D n v) : ℂ :=
  (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow (absEv D.host.F D.host.E v (aV p)) (z + (n : ℂ) / 2)

theorem lawV_mul (χ : (AE D)ˣ →* Circle) (z : ℂ) (p q : PV D n v) :
    lawV χ z (p * q) = lawV χ z p * lawV χ z q := by
  simp only [lawV, aV, map_mul, Circle.coe_mul, npow_mul]
  ring

theorem law_emb {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (p : PV D n v) (g : G D n) :
    f (emb D.sp.cm.sig (Jst D n) v p * g) = lawV χ z p * f g := by
  have h := hf (GlobalTheory.LocIntw.embUp v p).1 (GlobalTheory.LocIntw.embUp v p).2
    (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) rfl g
  have e : Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)) =
      ideleAt D.host.F D.host.E v (aV p) := GlobalTheory.LocIntw.aUp_embUp v p
  have e2 : absA D (ideleAt D.host.F D.host.E v (aV p)) = absEv D.host.F D.host.E v (aV p) := absE_ideleAt v _
  have e3 : (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (GlobalTheory.LocIntw.leviUp _ _ _ (GlobalTheory.LocIntw.embUp v p)))) (z + (n : ℂ) / 2) =
      lawV χ z p :=
    (congrArg (fun y => (χ y : ℂ) * npow (absA D y) (z + (n : ℂ) / 2)) e).trans
      (congrArg (fun r => (χ (ideleAt D.host.F D.host.E v (aV p)) : ℂ) * npow r (z + (n : ℂ) / 2)) e2)
  exact h.trans (congrArg (· * f g) e3)

theorem shift {χ : (AE D)ˣ →* Circle} {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f)
    (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) (g : G D n) (p₀ p₁ : PV D n v)
    {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v} (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀) {u : G D n} (hu : u ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (e₁ : k₀ * proj D.sp.cm.sig (Jst D n) v u = p₁ * k₁) : f (g * u) = lawV χ z p₁ * f g := by
  have embK : ∀ {k : GLoc D.sp.cm.sig (Jst D n) v}, k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v →
      emb D.sp.cm.sig (Jst D n) v k ∈ KAt D n v := fun hk =>
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  obtain ⟨uv, rfl⟩ : ∃ uv, emb D.sp.cm.sig (Jst D n) v uv = u := by
    rw [← range_emb] at hu; exact hu
  rw [proj_emb_self] at e₁
  obtain ⟨g', hg'⟩ : ∃ g' : G D n, g' = g * (emb D.sp.cm.sig (Jst D n) v (proj D.sp.cm.sig (Jst D n) v g))⁻¹ := ⟨_, rfl⟩
  have h1 : proj D.sp.cm.sig (Jst D n) v g' = 1 := by simp [hg']
  have h2 : g = g' * emb D.sp.cm.sig (Jst D n) v p₀ * emb D.sp.cm.sig (Jst D n) v k₀ := by
    rw [mul_assoc, ← map_mul, ← e₀, hg', inv_mul_cancel_right]
  have h3 : g * emb D.sp.cm.sig (Jst D n) v uv =
      g' * emb D.sp.cm.sig (Jst D n) v (p₀ * p₁) * emb D.sp.cm.sig (Jst D n) v k₁ := by
    rw [h2]
    simp only [mul_assoc, ← map_mul, e₁]
  have c : ∀ x : GLoc D.sp.cm.sig (Jst D n) v, g' * emb D.sp.cm.sig (Jst D n) v x = emb D.sp.cm.sig (Jst D n) v x * g' :=
    fun x => (commute_emb D.sp.cm.sig (Jst D n) x h1).symm.eq
  have h4 : f g = lawV χ z p₀ * f g' := by
    conv_lhs => rw [h2]
    rw [hK _ (embK hk₀), c, law_emb hf]
  rw [h3, hK _ (embK hk₁), c, show ((p₀ : GLoc D.sp.cm.sig (Jst D n) v) * p₁) = ((p₀ * p₁ : PV D n v) : GLoc D.sp.cm.sig (Jst D n) v) from rfl,
    law_emb hf, lawV_mul, h4]
  ring

def dV (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h : GLoc D.sp.cm.sig (Jst D n) v) : Fv D.host.F v :=
  splitProj τ (GlobalTheory.LocIntw.matR _ D.sp.cm.sig h).det

theorem dV_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (h h' : GLoc D.sp.cm.sig (Jst D n) v) :
    dV τ (h * h') = dV τ h * dV τ h' := by
  rw [dV, dV, dV, GlobalTheory.LocIntw.matR_mul, Matrix.det_mul, map_mul]

theorem dV_one (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : dV τ (1 : GLoc D.sp.cm.sig (Jst D n) v) = 1 := by
  rw [dV, GlobalTheory.LocIntw.matR_one, Matrix.det_one, map_one]

theorem det_mem_subring {R : Type} [CommRing R] (S : Subring R) {m : ℕ} {M : Matrix (Fin m) (Fin m) R}
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun s _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem map_blk_eq_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (b : Matrix (Fin n) (Fin n) A)
    (h : ∀ i j, φ (b i j) = 0) : (blk4 1 b 0 1).map φ = 1 := by
  rw [GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    show b.map φ = 0 from Matrix.ext h, StdUnn.Model.block_matrix_one]

theorem norm_dV_of_mem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {k : GLoc D.sp.cm.sig (Jst D n) v}
    (hk : k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) : ‖dV τ k‖ = 1 := by
  obtain ⟨h1, h2⟩ := mem_stabLoc_stdLattice_iff.1 hk
  have a1 : ‖dV τ k‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h1))
  have a2 : ‖dV τ k⁻¹‖₊ ≤ 1 := nnnorm_le_one_iff_mem.2 (splitProj_mem τ (det_mem_subring _ h2))
  have e : dV τ k * dV τ k⁻¹ = 1 := by rw [← dV_mul, mul_inv_cancel, dV_one]
  have b1 : ‖dV τ k‖ ≤ 1 := by exact_mod_cast a1
  have b2 : ‖dV τ k⁻¹‖ ≤ 1 := by exact_mod_cast a2
  have e' : ‖dV τ k‖ * ‖dV τ k⁻¹‖ = 1 := by rw [← norm_mul, e, norm_one]
  refine le_antisymm b1 ?_
  calc (1 : ℝ) = ‖dV τ k‖ * ‖dV τ k⁻¹‖ := e'.symm
    _ ≤ ‖dV τ k‖ * 1 := mul_le_mul_of_nonneg_left b2 (norm_nonneg _)
    _ = ‖dV τ k‖ := mul_one _

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (C : Cut D n v) {x : hermA D n} (hx : x ∈ C.s) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := by
  refine mem_atPts.2 ⟨mem_finPts_iff_forall.2 fun w => GlobalTheory.LocIntw.ext_matR ?_, fun u hu => GlobalTheory.LocIntw.ext_matR ?_⟩
  · refine (GlobalTheory.LocIntw.matR_mapH (evInf D.host.F w) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.inf x hx w i j
  · refine (GlobalTheory.LocIntw.matR_mapH (evFin D.host.F u) (nb x)).trans ?_
    rw [GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.matR_one]
    exact map_blk_eq_one _ _ fun i j => C.off x hx u (by simpa using hu) i j

theorem dV_nb (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) :
    dV τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = 1 := by
  have h : GlobalTheory.LocIntw.matR _ D.sp.cm.sig (proj D.sp.cm.sig (Jst D n) v (nb x)) = _ :=
    GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [dV, h, GlobalTheory.LocIntw.matR_adele, hnb x, GlobalTheory.LocIntw.blockMatrix_map, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), det_upper_triangular_block, Matrix.det_one, mul_one, map_one]

theorem norm_split_eq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (p : PV D n v) (hp : ‖dV τ p.1‖ = 1) :
    ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ := by
  obtain ⟨d, h1, h2⟩ := exists_det_parabolic (GlobalTheory.LocIntw.Jst_eq D n) p
  have h3 : ‖splitProj τ ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h1.symm).trans hp
  have h4 : ‖splitProj (τ.comp D.sp.cm.sig) ((aV p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ * ‖splitProj τ d‖ = 1 := by
    rw [splitProj_comp, ← norm_mul, ← map_mul]
    exact (congrArg (fun y => ‖splitProj τ y‖) h2).trans (by rw [map_one, norm_one])
  exact eq_of_mul_eq_one h3 h4

theorem chi_one {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {k₀ k₁ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (hk₁ : k₁ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v)
    {k : G D n} (hk : k ∈ KAt D n v) (x : hermA D n) (p₁ : PV D n v)
    (e : k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x) = p₁ * k₁) :
    χ (ideleAt D.host.F D.host.E v (aV p₁)) = 1 := by
  refine hχ _ (norm_split_eq τ p₁ ?_)
  have hk' : proj D.sp.cm.sig (Jst D n) v k ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v :=
    (GlobalTheory.LocIntw.mem_KUpAd.1 hk.1).1 v
  have h := congrArg (fun y => ‖dV τ y‖) e
  simp only [map_mul, dV_mul, dV_nb τ hnb, norm_mul, norm_one, norm_dV_of_mem τ hk₀, norm_dV_of_mem τ hk₁,
    norm_dV_of_mem τ hk', mul_one, one_mul] at h
  exact h.symm

end GlobalTheory.CompanionTheory.Jp.B3

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]


open scoped Pointwise in
theorem mean_add_left (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] {s : Set G}
    (hs : IsAddFundamentalDomain Γ s μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (t : G) :
    ∫ y in s, f (t + y) ∂μ = ∫ y in s, f y ∂μ := by
  have hFD : IsAddFundamentalDomain Γ (t +ᵥ s) μ := hs.vadd_of_comm t
  have h1 : ∫ y in (t +ᵥ s), f y ∂μ = ∫ y in s, f (t + y) ∂μ := by
    have hemb : MeasurableEmbedding (fun y : G => t + y) := (Homeomorph.addLeft t).measurableEmbedding
    exact (measurePreserving_add_left μ t).setIntegral_image_emb hemb f s
  rw [← h1]
  exact hFD.setIntegral_eq hs (fun g x => hf g.1 g.2 x)

theorem exists_bound_of_periodic (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    (f : G → ℂ) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov x
  rw [← hf γ hγ x]
  exact hC _ hk

theorem const_of_coefficients (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) (A : Type) [AddCommGroup A] (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a))
    (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y) (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1)
    (hn : ∀ a x, ‖χ a x‖ = 1) (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ∞) (φ : G → ℂ) (hφ : Continuous φ)
    (hper : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) (hco : ∀ a, a ≠ 0 → ∫ x in 𝓕, χ a x * φ x ∂μ = 0) (y : G) : φ y = φ 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨C, hC⟩ := exists_bound_of_periodic Γ hK hcov φ hφ hper
  have hint : ∀ (a : A) (f : G → ℂ), Continuous f → (∀ x, ‖f x‖ ≤ C) → IntegrableOn (fun x => χ a x * f x) 𝓕 μ := by
    intro a f hf hb
    refine Measure.integrableOn_of_bounded (M := C) hfin ((hc a).mul hf).aestronglyMeasurable (.of_forall fun x => ?_)
    rw [norm_mul, hn, one_mul]
    exact hb x
  have hshift : ∀ a, ∫ x in 𝓕, χ a x * φ (y + x) ∂μ = ∫ x in 𝓕, χ a x * φ x ∂μ := by
    intro a
    by_cases h : a = 0
    · subst h
      simp only [h0, one_mul]
      exact mean_add_left Γ μ h𝓕 φ hper y
    · have hp : ∀ γ ∈ Γ, ∀ x, χ a (γ + x) * φ (γ + x) = χ a x * φ x := fun γ hγ x => by
        rw [hper γ hγ, hx, (hker γ).2 hγ a, one_mul]
      have h1 := mean_add_left Γ μ h𝓕 (fun x => χ a x * φ x) hp y
      rw [hco a h] at h1 ⊢
      have h2 : ∫ x in 𝓕, χ a (y + x) * φ (y + x) ∂μ = χ a y * ∫ x in 𝓕, χ a x * φ (y + x) ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x => by simp only [hx, mul_assoc])
      rw [h2] at h1
      have hne : χ a y ≠ 0 := fun e => by simpa [e] using hn a y
      exact (mul_eq_zero.1 h1).resolve_left hne
  have hφy : Continuous fun x => φ (y + x) := hφ.comp (continuous_const.add continuous_id)
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha h0 hn hker μ 𝓕 hμ h𝓕
    (fun x => φ (y + x) - φ x) (hφy.sub hφ)
    (fun γ hγ x => by
      show φ (y + (γ + x)) - φ (γ + x) = φ (y + x) - φ x
      rw [add_left_comm, hper γ hγ, hper γ hγ])
    (fun a => by
      have e : ∀ x, χ a x * (φ (y + x) - φ x) = χ a x * φ (y + x) - χ a x * φ x := fun x => mul_sub _ _ _
      simp only [e]
      rw [integral_sub (hint a _ hφy fun x => hC _) (hint a _ hφ hC), hshift a, sub_self])
  have h := congrFun key 0
  simp only [add_zero, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Abstract


set_option synthInstance.maxHeartbeats 400000 in
theorem const_of_coeff : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p →
    ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ →
    (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  intro D p lp 𝓖p hC ψ hψ φ hφ hper hco y
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D p) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D p) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := p)
  refine const_of_coefficients (ratHerm D p) K hK hcov (GlobalTheory.CompanionTheory.FourierN.hermSub D p) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩), fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lp 𝓖p hlam hFD (by rw [h1]; exact ENNReal.one_ne_top) φ hφ hper
    (fun a ha => (integral_congr_ae (.of_forall fun x => mul_comm _ _)).trans
      (hco ⟨a.1, a.2⟩ (fun e => ha (Subtype.ext e)))) y

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbedding
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

open GlobalTheory.StdUnn.Model
open GlobalTheory.CompanionTheory.JacobiMaps (b11 b12 b21 b22 block_matrix_of_blocks upperLeft_block upperRight_block lowerLeft_block_entry lowerRight_block continuous_block_matrix continuous_bl
  block_mul₂ bl_add block_sub blockRowSubstitution_one blockMatrix_zero blockMatrix_neg_one adj_bl adjoint_symplectic_block_product mkG isU_mat)

variable {D : D7} {n ρ p : ℕ}

def firstM (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn (b11 M) 0 0 1) (bl hn (b12 M) 0 0 0) (bl hn (b21 M) 0 0 0) (bl hn (b22 M) 0 0 1)

theorem first_block_embedding_block (hn : ρ + p = n) (a b c d : Mx D ρ ρ) :
    firstM hn (blk4 a b c d) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  rw [firstM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def firstMon (hn : ρ + p = n) : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n) where
  toFun := firstM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := ρ), first_block_embedding_block, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, first_block_embedding_block, first_block_embedding_block, first_block_embedding_block, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem firstM_isU (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (ρ + ρ) (ρ + ρ)) = blk4 0 1 (-1) 0) :
    (adj (firstM hn M) * blk4 0 1 (-1) 0 * firstM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [first_block_embedding_block, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def firstF (hn : ρ + p = n) (g : G D ρ) : G D n :=
  mkG (Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g)) (firstM_isU hn _ (isU_mat g))

theorem matHom_firstF (hn : ρ + p = n) (g : G D ρ) :
    matHom _ D.sp.cm.sig (Jst D n) (firstF hn g) = Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) := rfl

def firstG (hn : ρ + p = n) : G D ρ →* G D n where
  toFun := firstF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_firstF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_firstF, matHom_firstF, matHom_firstF, map_mul, map_mul])

theorem mat_firstG (hn : ρ + p = n) (h : G D ρ) : mat (firstG hn h) = firstM hn (mat h) := rfl

theorem continuous_firstM (hn : ρ + p = n) : Continuous (firstM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const
      continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)

theorem continuous_firstG (hn : ρ + p = n) : Continuous (firstG (D := D) hn) := by
  have h0 : Continuous (Units.map (firstMon (D := D) hn : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_firstM hn)
  have h : Continuous fun g : G D ρ => Units.map (firstMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D ρ)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

end GlobalTheory.CompanionTheory.FirstBlockEmb

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

theorem exists_first_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  intro D n ρ p hn
  refine ⟨firstG hn, continuous_firstG hn, fun h a b c d e => ?_⟩
  exact (mat_firstG hn h).trans ((congrArg (firstM hn) e).trans (first_block_embedding_block hn a b c d))

end GlobalTheory.CompanionTheory.FirstBlockEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficientStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariance_of_constant_fourier_coefficient : ∀ (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p) (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)), CoefData (D := D) (n := p) nb lam 𝓖 → ∀ (F : G D p → ℂ), Continuous F → LeftInv (GF D p) F → ∀ β : HermE D p, β.1 = 0 → (∀ g, fc ψ lam 𝓖 nb F β g = F g) → ∀ (b : hermA D p) (g : G D p), F (nb b * g) = F g := by
  first | exact @GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | exact GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const | (intros; apply GlobalTheory.CompanionTheory.ConstN.nb_inv_of_const <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_multisegments_of_exhaustion_gl : (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k) → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.LanglandsMultisegments := by
  first | exact @GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | exact GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | (intros; apply GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUnipotentMean
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcNb

theorem nzx_mul_nb {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) {nb : hermA D n → G D n} (h : IsNMap nb)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    M.nzx z 0 * (M.nzx 0 x * nb (bT hn 0 0 y)) = nb (bT hn z x y) := by
  rw [← mul_assoc, GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero, zero_add]
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', M.nzx_mat, h, h, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
  congr 1
  show bl hn z.1 x (adj x) 0 + bl hn (0 : Mx D ρ ρ) 0 (adj 0) y.1 = bl hn z.1 x (adj x) y.1
  rw [GlobalTheory.CompanionTheory.PcB.blockMatrix_add', adj_zero]
  simp

theorem pc_nb : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) {nb : hermA D n → G D n}, IsNMap nb → ∀ (g : G D n) (y : hermA D p), pc M m ψ b₀ F (nb (bT hn 0 0 y) * g) = pm hn m ψ b₀ (fun b => F (nb b * g)) y := by
  intro D n ρ p hn M m ψ b₀ F nb h g y
  show ∫ x in m.𝓕, ∫ z in m.𝓖, F (M.nzx z 0 * (M.nzx 0 x * (nb (bT hn 0 0 y) * g))) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ =
    ∫ x in m.𝓕, ∫ z in m.𝓖, F (nb (bT hn z x y) * g) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show F (M.nzx z 0 * (M.nzx 0 x * (nb (bT hn 0 0 y) * g))) * _ = F (nb (bT hn z x y) * g) * _
  rw [← nzx_mul_nb M h z x y]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.PcNb
end
end

