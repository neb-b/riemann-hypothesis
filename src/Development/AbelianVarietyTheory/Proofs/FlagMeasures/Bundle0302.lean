module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSum
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mass.Transp

theorem orbSum_img : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he φ hφ L
  have hinv : ∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V),
      φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M) := by
    intro s M
    have hs := img_smul (R := 𝓞 K) e he s M
    erw [hs, hφ]
  have hgen : ∀ M : Submodule (𝓞 K) V,
      GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L := by
    intro M
    constructor
    · intro hM
      have := genus_img e.symm (symm_isom e he) _ _ hM
      rwa [img_symm_img, img_symm_img] at this
    · exact genus_img e he L M
  refine ⟨hinv, hgen, ?_⟩
  symm
  refine GlobalTheory.Mass.OrbTransport.main _ _ _ _ (conj e he) (img e) _ _ φ (genus_stable _) (genus_stable _) ?_
    (fun g x _ => img_smul e he g x) hφ
  refine ⟨fun M hM => (hgen M).2 hM, fun a _ b _ hab => ?_, fun M hM => ⟨img e.symm M, ?_, img_img_symm e M⟩⟩
  · rw [← img_symm_img e a, hab, img_symm_img]
  · rw [← hgen, img_img_symm]; exact hM

end GlobalTheory.Mass.Transp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicOrthogonalDecomposition
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

section Abstract

variable {G H L : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [CompleteSpace H] in
theorem inner_of_norm (A : H →L[ℂ] H) (hA : ∀ u, ‖A u‖ = ‖u‖) (x y : H) : ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := { toLinearMap := (A : H →ₗ[ℂ] H), norm_map' := hA }
  exact e.inner_map_map x y

theorem inner_intertwiners (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g u, ‖σ g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, σ g u ∈ S) → S = ⊥ ∨ S = ⊤)
    (R : G → (L →L[ℂ] L)) (hR : ∀ g u, ‖R g u‖ = ‖u‖) (w : H) (hw : ‖w‖ = 1)
    (T T' : H →L[ℂ] L) (hT : ∀ g, T.comp (σ g) = (R g).comp T) (hT' : ∀ g, T'.comp (σ g) = (R g).comp T')
    (u u' : H) : ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ := by
  have hinv : ∀ g (v : H), σ g (σ g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  have hSin : ∀ v x, ⟪v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ = ⟪T v, T' x⟫_ℂ := by
    intro v x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have hcomm : ∀ g, (ContinuousLinearMap.adjoint T) ∘L T' * σ g = σ g * ((ContinuousLinearMap.adjoint T) ∘L T') := by
    intro g
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hSin]
    have h1 : T v = R g (T (σ g⁻¹ v)) := by
      have := congrArg (fun F : H →L[ℂ] L => F (σ g⁻¹ v)) (hT g)
      simp only [ContinuousLinearMap.comp_apply, hinv] at this
      exact this
    have h2 : T' (σ g x) = R g (T' x) := by
      have := congrArg (fun F : H →L[ℂ] L => F x) (hT' g)
      simpa only [ContinuousLinearMap.comp_apply] using this
    have h3 : ⟪v, σ g (((ContinuousLinearMap.adjoint T) ∘L T') x)⟫_ℂ
        = ⟪σ g⁻¹ v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ := by
      conv_lhs => rw [← hinv g v]
      exact inner_of_norm (σ g) (hσ g) _ _
    rw [h3, hSin, h1, h2, inner_of_norm (R g) (hR g)]
  obtain ⟨c, hc⟩ := GlobalTheory.schur_unitary_irreducible G H σ hσ hirr _ hcomm
  have key : ∀ a b, ⟪T a, T' b⟫_ℂ = c * ⟪a, b⟫_ℂ := by
    intro a b
    rw [← hSin, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  rw [key, key w w, hww, mul_one]


omit [CompleteSpace H] [CompleteSpace L] in
theorem exists_frame (V : Submodule ℂ (H →L[ℂ] L)) [FiniteDimensional ℂ V] (w : H)
    (hV : ∀ T ∈ V, ∀ T' ∈ V, ∀ u u', ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ) :
    ∃ T : Fin (Module.finrank ℂ V) → (H →L[ℂ] L), (∀ i, T i ∈ V) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧
      (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = V := by
  classical
  let Φ : V →ₗ[ℂ] L := (ContinuousLinearMap.apply ℂ L w : (H →L[ℂ] L) →ₗ[ℂ] L) ∘ₗ V.subtype
  have hΦ : ∀ T : V, Φ T = (T : H →L[ℂ] L) w := fun T => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun u => ?_
    have h := hV T T.2 T T.2 u u
    rw [← hΦ, hT, inner_zero_left, zero_mul] at h
    simpa using (inner_self_eq_zero.mp h)
  have hdim : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ V :=
    (LinearEquiv.ofInjective Φ hinj).finrank_eq.symm
  let b := (stdOrthonormalBasis ℂ (LinearMap.range Φ)).reindex (finCongr hdim)
  have he : ∀ x, (((LinearEquiv.ofInjective Φ hinj).symm x : V) : H →L[ℂ] L) w = (x : L) := by
    intro x
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective Φ hinj).apply_symm_apply x)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hin : ∀ i j u u', ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
      (((LinearEquiv.ofInjective Φ hinj).symm (b j) : V) : H →L[ℂ] L) u'⟫_ℂ
      = (if i = j then 1 else 0) * ⟪u, u'⟫_ℂ := by
    intro i j u u'
    rw [hV _ ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2 _ ((LinearEquiv.ofInjective Φ hinj).symm (b j)).2,
      he, he, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal i j]
  refine ⟨fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L),
    fun i => ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2, ?_, ?_, ?_⟩
  · intro i u
    have h : ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
        (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [hin]
      simp
    have h2 : ‖(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    nlinarith [norm_nonneg ((((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u), norm_nonneg u]
  · intro i j hij u u'
    rw [hin]
    simp [hij]
  · have hbasis : Submodule.span ℂ (Set.range fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) = ⊤ := by
      have := (b.toBasis.map (LinearEquiv.ofInjective Φ hinj).symm).span_eq
      rw [← this, Module.Basis.coe_map, OrthonormalBasis.coe_toBasis]
      rfl
    have hr : Set.range (fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L))
        = V.subtype '' Set.range (fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hbasis, Submodule.map_top, Submodule.range_subtype]

end Abstract

theorem exists_orthonormal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R → ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re := by
  intro B d hd hfin hle
  haveI := hfin
  obtain ⟨hU, hI, -, hw, -⟩ := _root_.GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨h1, hmul, hnorm, -⟩ := hU
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := h1, map_mul' := fun a b => hmul a b }
  have hR := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.1
  have hirr : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ u ∈ S, σ g u ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hSinv
    have hI' : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ v ∈ S, B.σs g v ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
      simpa [IsIrr] using hI
    exact hI' S hS hSinv
  have hV : ∀ T ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ T' ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ u u',
      ⟪T u, T' u'⟫_ℂ = ⟪T (B.tens B.w), T' (B.tens B.w)⟫_ℂ * ⟪u, u'⟫_ℂ := by
    intro T hT T' hT' u u'
    exact inner_intertwiners σ (fun g u => hnorm g u) hirr (fun g => B.R (g, 1)) (fun g u => hR (g, 1) u)
      (B.tens B.w) hw T T' (fun g => hle hT g) (fun g => hle hT' g) u u'
  exact exists_frame (B.I.eHom B.σs B.μf B.fund B.R B.Re) (B.tens B.w) hV

end GlobalTheory.IntertwinerFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaFactorsNearOneGivenCompactFactor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwNear

open GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem nrm_J_conj (X : Matrix (Fin n) (Fin n) ℂ) : nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by
  unfold nrm Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

private theorem uMat_inv_eq_Jm_conjTranspose_Jm (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hg : (uMat g)ᴴ * (Formalism.REAL.Jm ε * uMat g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by simp [uMat]
  have h2 : Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, J_sq]
  calc uMat g⁻¹ = (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
        rw [h2, Matrix.one_mul]
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := Matrix.mul_assoc _ _ _
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h1, Matrix.mul_one]

theorem nrm_inv (g : Formalism.REAL.UJ ε) : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
  have e : uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
    rw [uMat_inv_eq_Jm_conjTranspose_Jm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, J_sq]
  rw [e, nrm_J_conj, nrm_conjTranspose]

theorem nrm_mul_sub_one (g h : Formalism.REAL.UJ ε) :
    nrm (uMat (g * h) - 1) ≤ nrm (uMat g - 1) * nrm (uMat h - 1) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
  have e : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
    rw [show uMat (g * h) = uMat g * uMat h from rfl]
    noncomm_ring
  rw [e]
  calc _ ≤ nrm ((uMat g - 1) * (uMat h - 1) + (uMat g - 1)) + nrm (uMat h - 1) := nrm_add_le _ _
    _ ≤ nrm ((uMat g - 1) * (uMat h - 1)) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
        gcongr
        exact nrm_add_le _ _
    _ ≤ _ := by
        gcongr
        exact nrm_mul_le _ _

theorem nrm_levi_le {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    {u m : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε W) (hm : m ∈ flagM ε W) :
    nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := by

  obtain ⟨hN, hM⟩ := _root_.GlobalTheory.IwConst.FlagMem.lowers_keeps n ε a j W hW
  obtain ⟨htr, -, -, hmul⟩ := _root_.GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps n ε a j W hW
  have hX := hN u hu
  obtain ⟨hm1, hm2⟩ := hM m hm
  have hY : uMat m * (uMat m)ᴴ - uMat m ∈ keeps ε W := sub_mem (hmul _ hm1 _ hm2) hm1
  have e : uMat (u * m) - 1 = (uMat u - 1) * uMat m + (uMat m - 1) := by
    rw [show uMat (u * m) = uMat u * uMat m from rfl]
    noncomm_ring
  have key : ((((uMat u - 1) * uMat m) * (uMat m - 1)ᴴ).trace).re = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      htr _ hX _ hY, Complex.zero_re]
  have hh : Formalism.REAL.hs (uMat m - 1) ≤ Formalism.REAL.hs (uMat (u * m) - 1) := by
    rw [e, hs_add, key]
    linarith [hs_nonneg ((uMat u - 1) * uMat m)]
  exact Real.sqrt_le_sqrt hh

theorem near : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k : Formalism.REAL.UJ ε, nrm (uMat (u * m * k) - 1) ≤ ρ → nrm (uMat k - 1) < ρ → nrm (uMat u - 1) < t ∧ nrm (uMat m - 1) < t ∧ nrm (uMat k - 1) < t := by
  intro n ε a j W hW t ht
  obtain ⟨ρ, hρ0, hρ1, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧ ρ ≤ t / 10 :=
    ⟨min (1 / 3) (t / 10), lt_min (by norm_num) (by linarith), min_le_left _ _, min_le_right _ _⟩
  refine ⟨ρ, hρ0, ?_⟩
  intro u hu m hm k hx hk
  have hK0 := nrm_nonneg (uMat k - 1)

  have hA : nrm (uMat (u * m) - 1) ≤ ρ * ρ + 2 * ρ := by
    have h := nrm_mul_sub_one (u * m * k) k⁻¹
    rw [mul_inv_cancel_right, nrm_inv] at h
    have : nrm (uMat (u * m * k) - 1) * nrm (uMat k - 1) ≤ ρ * ρ := mul_le_mul hx hk.le hK0 hρ0.le
    linarith

  have hM : nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := nrm_levi_le hW hu hm
  have hM0 := nrm_nonneg (uMat m - 1)
  have hU : nrm (uMat u - 1) ≤
      nrm (uMat (u * m) - 1) * nrm (uMat m - 1) + nrm (uMat (u * m) - 1) + nrm (uMat m - 1) := by
    have h := nrm_mul_sub_one (u * m) m⁻¹
    rwa [mul_inv_cancel_right, nrm_inv] at h
  have hρρ : ρ * ρ ≤ ρ / 3 := by nlinarith
  have hs0 : 0 ≤ ρ * ρ + 2 * ρ := by positivity
  have hs1 : ρ * ρ + 2 * ρ ≤ 1 := by linarith
  have hprod : nrm (uMat (u * m) - 1) * nrm (uMat m - 1) ≤ ρ * ρ + 2 * ρ :=
    calc _ ≤ (ρ * ρ + 2 * ρ) * (ρ * ρ + 2 * ρ) := mul_le_mul hA (hM.trans hA) hM0 hs0
      _ ≤ ρ * ρ + 2 * ρ := mul_le_of_le_one_left hs0 hs1
  exact ⟨by linarith, by linarith, by linarith⟩

end GlobalTheory.IwNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolume
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem gau_definite_and_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  intro n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  obtain ⟨Q, ι, hQ, hh⟩ := GlobalTheory.IwConst.Adapted.exists_adapted n dN dM dK dL EN EM EK EL hN hM hK hL hR hd
  have sq0 : ∀ {d : ℕ} (f : Fin d → ℝ), ∑ i, f i ^ 2 ≤ 0 → f = 0 := by
    intro d f hf
    funext i
    have h0 : ∑ i, f i ^ 2 = 0 := le_antisymm hf (by positivity)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).1 h0 i (Finset.mem_univ i)
    simpa using this
  constructor
  · rintro ⟨x, y, z⟩ hv
    obtain ⟨h1, h2⟩ := hh x y z
    have a1 : nrm (cmb EN x + cmb EM y + cmb EK z) ≤ 0 := (le_max_left _ _).trans hv.le
    have a2 : len (crd EL (cmb EK z)) ≤ 0 := (le_max_right _ _).trans hv.le
    have b1 : Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) = 0 := by
      rw [← nrm_sq, le_antisymm a1 (nrm_nonneg _)]; simp
    have b2 : ∑ i, (Q z).2 i ^ 2 = 0 := by
      rw [← h2, ← len_sq, le_antisymm a2 (len_nonneg _)]; simp
    rw [b1] at h1
    have p1 : 0 ≤ ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, (y i + ι (Q z).2 i) ^ 2 := by positivity
    have p3 : 0 ≤ ∑ i, (Q z).1 i ^ 2 := by positivity
    rw [← Finset.sum_div] at h1
    have hz : z = 0 := sq0 z (by rw [← hQ z]; linarith)
    subst hz
    have hx : x = 0 := sq0 x (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    have hy : y = 0 := sq0 y (by
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1 p1 p2
      linarith)
    subst hx hy
    rfl
  · have hmp := GlobalTheory.IwConst.measurePreserving_of_sum_sq_eq dK dN dL hd Q hQ
    have hmp2 : MeasurePreserving (Prod.map id (Prod.map id Q) :
        (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) →
          (Fin dN → ℝ) × (Fin dM → ℝ) × ((Fin dN → ℝ) × (Fin dL → ℝ))) volume volume :=
      (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hmp)
    rw [← GlobalTheory.IwConst.Shear.volume_sheared_balls dN dM dL ι, ← hmp2.measure_preimage]
    · congr 1
      ext ⟨x, y, z⟩
      obtain ⟨h1, h2⟩ := hh x y z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map, id, gau, max_le_iff, nrm, len,
        Real.sqrt_le_one, h1, h2]
    · refine (IsClosed.measurableSet ?_).nullMeasurableSet
      have hι : Continuous ι := ι.continuous_of_finiteDimensional
      refine IsClosed.and (isClosed_le ?_ continuous_const) (isClosed_le ?_ continuous_const)
      · fun_prop
      · fun_prop

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePosition
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.LiePos

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) : Formalism.REAL.inG ε Xᴴ := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have hJ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← mul_assoc, hJ, one_mul]
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_conjTranspose]
  have e := congrArg (fun M => Formalism.REAL.Jm ε * M * Formalism.REAL.Jm ε) h
  simp only [mul_add, add_mul, mul_assoc, hJ, hJ', mul_one, mul_zero, zero_mul] at e
  rw [add_comm]
  exact e

theorem inG_sub {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) (k : Formalism.REAL.inG ε Y) :
    Formalism.REAL.inG ε (X - Y) := by
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_sub, sub_mul, mul_sub]
  rw [show Xᴴ * Formalism.REAL.Jm ε - Yᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * X - Formalism.REAL.Jm ε * Y) =
      (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) - (Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y) by abel, h, k, sub_zero]

theorem comm_of_maxK {g : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) :
    uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp hg
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hU]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h1, one_mul]

theorem skew_of_comm {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X)
    (hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : Xᴴ = -X := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have h' : Xᴴ * Formalism.REAL.Jm ε = -(X * Formalism.REAL.Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [h']
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

theorem exp_unitary {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Z))ᴴ * NormedSpace.exp ((t : ℂ) • Z) = 1 := by
  have hA : ((t : ℂ) • Z)ᴴ = -((t : ℂ) • Z) := by
    rw [conjTranspose_smul, hZ, smul_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((t : ℂ) • Z)) ((t : ℂ) • Z) := (Commute.refl _).neg_left
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

theorem mem_span_of_subset {S S' : Set (Formalism.REAL.UJ ε)} {d d' : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {E' : Fin d' → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) (h' : IsCut ε S' E') (hS : S ⊆ S') (i : Fin d) :
    E i ∈ Submodule.span ℝ (Set.range E') := by
  obtain ⟨A', -, -, hA', hS'⟩ := h'
  have hT : E i ∈ A' := (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε S d E h).2.1 A' (fun g hg => by
    have hg' : g ∈ S' := hS hg
    rw [hS'] at hg'
    exact hg') i
  exact (hA' _).1 ⟨hT, h.inG (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem lieRel : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL
  obtain ⟨hlow, hkeep⟩ := _root_.GlobalTheory.IwConst.FlagMem.lowers_keeps n ε a j W hW
  obtain ⟨htr, hle, hone, -⟩ := _root_.GlobalTheory.IwConst.FlagTrace.trace_lowers_keeps n ε a j W hW
  have hENlow : ∀ i, EN i ∈ lowers ε W := (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε _ dN EN hN).2.1 (lowers ε W) hlow
  have hEMkeep : ∀ k, EM k ∈ keeps ε W :=
    (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε _ dM EM hM).2.1 (keeps ε W) (fun m hm => sub_mem (hkeep m hm).1 hone)
  have hEMstar : ∀ k, (EM k)ᴴ ∈ keeps ε W := by
    let T2 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := {Y | Yᴴ ∈ keeps ε W}
        add_mem' := fun {A B} hA hB => by
          simp only [Set.mem_ofPred_eq, conjTranspose_add] at *
          exact add_mem hA hB
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, conjTranspose_zero]
          exact zero_mem _
        smul_mem' := fun c Y hY => by
          simp only [Set.mem_ofPred_eq] at *
          rw [conjTranspose_smul, star_trivial]
          exact Submodule.smul_mem _ c hY }
    exact (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε _ dM EM hM).2.1 T2 (fun m hm => by
      change (uMat m - 1)ᴴ ∈ keeps ε W
      rw [conjTranspose_sub, conjTranspose_one]
      exact sub_mem (hkeep m hm).2 hone)
  let TC : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Y | Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y}
      add_mem' := fun {A B} hA hB => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_mul, mul_add, hA, hB]
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_mul_assoc, mul_smul_comm, hY] }
  have hEK : ∀ i, EK i ∈ TC := (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε _ dK EK hK).2.1 TC (fun g hg => by
    change (uMat g - 1) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (uMat g - 1)
    rw [sub_mul, mul_sub, one_mul, mul_one, comm_of_maxK hg])
  have hspan : Submodule.span ℝ (Set.range EK) ≤ TC :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hEK i)
  have hELK : ∀ i, EL i ∈ Submodule.span ℝ (Set.range EK) :=
    mem_span_of_subset hL hK Set.inter_subset_left
  refine ⟨fun i k => htr _ (hENlow i) _ (hEMstar k), fun i k => htr _ (hENlow i) _ (hEMkeep k),
    fun i k => htr _ (hENlow i) _ (hle (hENlow k)), mem_span_of_subset hL hM Set.inter_subset_right, hELK,
    fun i => skew_of_comm (hK.inG (hELK i)) (hspan (hELK i)), fun i => ?_⟩
  have hG : Formalism.REAL.inG ε (EN i) := hN.inG (Submodule.subset_span ⟨i, rfl⟩)
  have hY : Formalism.REAL.inG ε (EN i - (EN i)ᴴ) := inG_sub hG (inG_conjTranspose hG)
  have hskew : (EN i - (EN i)ᴴ)ᴴ = -(EN i - (EN i)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
  refine (_root_.GlobalTheory.IwTangent.lie_algebra_of_isCut n ε _ dK EK hK).2.2 _ hY (fun t g hg => ?_)
  change (uMat g)ᴴ * uMat g = 1
  rw [hg]
  exact exp_unitary hskew t

end GlobalTheory.IwConst.LiePos
end

