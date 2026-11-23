module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousGrpHom
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.CompactDualSwap

variable {P Q P' Q' : ℕ}

def AntiIso (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') : Prop :=
  (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = -Formalism.UG.Jpq P' Q'

theorem AntiIso.symm {e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q'} (h : AntiIso e) : AntiIso e.symm := by
  unfold AntiIso at *
  ext i j
  have := congrFun (congrFun h (e i)) (e j)
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.neg_apply, Equiv.symm_symm] at *
  rw [this, neg_neg]

def grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q →* UpqT P' Q' :=
  let f : Formalism.UG.Upq P Q →* GL (Fin P' ⊕ Fin Q') ℂ :=
    (Units.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom).comp (Formalism.UG.Upq P Q).subtype
  let f' : Formalism.UG.Upq P Q →* Formalism.UG.Upq P' Q' := f.codRestrict _ (by
    rintro ⟨g, hg⟩
    change Formalism.UG.cT _ g.val * _ * g.val = _ at hg
    change Formalism.UG.cT _ (g.val.submatrix e.symm e.symm) * _ *
      (g.val.submatrix e.symm e.symm) = _
    have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
      rw [h, neg_neg]
    have h3 : Formalism.UG.cT (starRingEnd ℂ) (g.val.submatrix e.symm e.symm) =
      (Formalism.UG.cT (starRingEnd ℂ) g.val).submatrix e.symm e.symm := rfl
    rw [h2, h3, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hg])
  f'

theorem mat_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (g : UpqT P Q) :
    (grpHom e h g).mat = g.mat.submatrix e.symm e.symm := rfl

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → _) :=
  (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective

theorem continuous_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) :
    Continuous (grpHom e h) := by
  rw [(GlobalTheory.UpqTopology.upq_lcsc P' Q').2.2.2.2.2.isInducing.continuous_iff]
  exact ((GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.continuous).matrix_submatrix e.symm e.symm

def grpEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q ≃ₜ* UpqT P' Q' where
  toFun := grpHom e h
  invFun := grpHom e.symm h.symm
  left_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  right_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  map_mul' := map_mul _
  continuous_toFun := continuous_grpHom e h
  continuous_invFun := continuous_grpHom e.symm h.symm

theorem lie_mem (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    X.val.submatrix e.symm e.symm ∈ lieU P' Q' := by
  have hX : X.valᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.val = 0 := X.2
  change (X.val.submatrix e.symm e.symm)ᴴ * Formalism.UG.Jpq P' Q' +
    Formalism.UG.Jpq P' Q' * X.val.submatrix e.symm e.symm = 0
  have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
    rw [h, neg_neg]
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← neg_add, neg_eq_zero]
  have := congrArg (fun M => Matrix.submatrix M e.symm e.symm) hX
  exact this

def lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : lieU P Q ≃L[ℝ] lieU P' Q' where
  toFun X := ⟨_, lie_mem e h X⟩
  invFun X := ⟨_, lie_mem e.symm h.symm X⟩
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := rfl
  map_smul' c X := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix e.symm e.symm).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix e e).subtype_mk _

theorem coe_lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    ((lieEquiv e h X : lieU P' Q') : Matrix _ _ ℂ) = X.val.submatrix e.symm e.symm := rfl

theorem mem_ball (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) (r : ℝ) :
    lieEquiv e h X ∈ ballU P' Q' r ↔ X ∈ ballU P Q r := by
  simp only [ballU, Set.mem_ofPred_eq, coe_lieEquiv, submatrix_apply]
  have : ∑ i, ∑ j, ‖X.val (e.symm i) (e.symm j)‖ = ∑ i, ∑ j, ‖X.val i j‖ := by
    rw [← e.symm.sum_comp (fun i => ∑ j, ‖X.val i j‖)]
    exact Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X.val (e.symm i) j‖)
  rw [this]

open scoped Matrix.Norms.Operator in
theorem exp_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (X.submatrix e.symm e.symm) = (NormedSpace.exp X).submatrix e.symm e.symm :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (continuous_id.matrix_submatrix e.symm e.symm) X).symm

theorem isOmegaLeb_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (lam : Measure (lieU P Q)) (hl : IsOmegaLeb lam) : IsOmegaLeb (lam.map (lieEquiv e h)) := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl
  refine ⟨(lieEquiv e h).isAddHaarMeasure_map lam, ?_⟩
  have hm : Measurable (lieEquiv e h) := (lieEquiv e h).continuous.measurable
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hv := volume_measurePreserving_piCongrLeft
    (fun _ : (Fin P' ⊕ Fin Q') × (Fin P' ⊕ Fin Q') => ℂ) (e.prodCongr e)
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P' Q').measurable (hm.prodMap hm),
    ← hv.map_eq, ← h2, Measure.map_map hv.measurable (hc P Q).measurable]
  congr 1
  funext ab ij
  obtain ⟨ij, rfl⟩ := (e.prodCongr e).surjective ij
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  simp [Formalism.BasicNotions.entries, coe_lieEquiv]

theorem omegaDensity_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (μ : Measure (UpqT P Q)) (c : ENNReal) (hμ : OmegaDensity μ c) :
    OmegaDensity (μ.map (grpEquiv e h)) c := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : BorelSpace (UpqT P' Q') := ⟨rfl⟩
  obtain ⟨lam, hl, ht⟩ := hμ
  refine ⟨_, isOmegaLeb_map e h lam hl, ?_⟩
  refine ht.congr fun r => ?_
  have e1 := (grpEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := μ)
  have e2 := (lieEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := lam)
  congr 1
  · refine Eq.trans ?_ (e1 _).symm
    congr 1
    ext g
    change (∃ X ∈ ballU P Q r, _) ↔ ∃ X ∈ ballU P' Q' r, g.mat.submatrix e.symm e.symm = _
    rw [(lieEquiv e h).surjective.exists]
    refine exists_congr fun X => ?_
    rw [mem_ball, coe_lieEquiv, exp_submatrix]
    refine and_congr_right fun _ => ⟨fun hh => by rw [hh], fun hh => ?_⟩
    ext i j
    simpa using congrFun (congrFun hh (e i)) (e j)
  · refine Eq.trans ?_ (e2 _).symm
    congr 1
    ext X
    exact (mem_ball e h X r).symm

def swapIdx (N : ℕ) : Fin 0 ⊕ Fin N ≃ Fin (0 + N) ⊕ Fin 0 :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (finCongr (Nat.zero_add N).symm) (Equiv.refl _))

theorem antiIso_swapIdx (N : ℕ) : AntiIso (swapIdx N) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [swapIdx, Formalism.UG.Jpq, Matrix.one_apply, Fin.ext_iff]
    · exact j.elim0
  · exact i.elim0

theorem cd_zero_univ : ∀ (c : CDHaar) (N : ℕ), c.cd 0 N Set.univ = 1 := by
  intro c N
  obtain ⟨d, hd0, hdt, h1, h2⟩ := c.trick 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (0 + N) 0
  have := c.haar 0 N
  have := c.haar (0 + N) 0
  have := c.prob (0 + N)
  let G := grpEquiv (swapIdx N) (antiIso_swapIdx N)
  have : ((c.cd 0 N).map G).IsHaarMeasure := G.isHaarMeasure_map _
  have h3 := omegaDensity_map _ (antiIso_swapIdx N) _ _ h1
  have h4 := Measure.isMulLeftInvariant_eq_smul ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  set a := Measure.haarScalarFactor ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  have h5 : OmegaDensity ((c.cd 0 N).map G) (a * d) := by
    rw [h4]; exact (_root_.GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul _ _ _ _ h2).2 a
  have h6 : (a : ENNReal) * d = 1 * d := by
    rw [one_mul]; exact (_root_.GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul _ _ _ _ h3).1 _ h5
  have h7 : (a : ENNReal) = 1 := (ENNReal.mul_left_inj hd0 hdt).1 h6
  have h8 : ((c.cd 0 N).map G) Set.univ = 1 := by
    rw [h4, Measure.smul_apply, measure_univ, ENNReal.smul_def, h7, one_smul]
  have hG : Measurable G := G.continuous.measurable
  rwa [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h8

end GlobalTheory.CompactDualSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

noncomputable section

namespace GlobalTheory.Mem.Col2.ChiFacLaw

open GlobalTheory.PeriodTransport GlobalTheory.IdealTransport

theorem detId_image (D : D7) {n : ℕ} (L₀ L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (G G' : Matrix (Fin n) (Fin n) D.host.E) (hu : G * G' = 1)
    (h : ∀ x ∈ L, G.mulVec x ∈ L') (h' : ∀ x ∈ L', G'.mulVec x ∈ L) :
    TaylorLogMetric.detId D L₀ L' = Submodule.span (𝓞 D.host.E) {G.det} * TaylorLogMetric.detId D L₀ L := by
  unfold TaylorLogMetric.detId
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(G' * A).det, ⟨_, fun v hv => ?_, rfl⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      exact h' _ (hA v hv)
    · show G.det * (G' * A).det = A.det
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨G * A, fun v hv => ?_, (Matrix.det_mul _ _).symm⟩
    rw [← Matrix.mulVec_mulVec]
    exact h _ (hA v hv)

theorem norm_one_span (D : D7) (z : D.host.E) (hz : z * D.host.conj z = 1) :
    TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {z}) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← hst] at hz
  have key : ∀ w x : D.host.E, x ∈ Submodule.span (𝓞 D.host.E) {w} → star x ∈ Submodule.span (𝓞 D.host.E) {star w} := by
    intro w x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨⟨star (r : D.host.E), r.2.map (starRingEnd D.host.E).toIntAlgHom⟩, ?_⟩
    exact (star_mul' (r : D.host.E) w).symm
  refine ⟨Submodule.span (𝓞 D.host.E) {star z}, fun x => ?_, ?_⟩
  · rw [← hst]
    exact ⟨fun h => by simpa using key _ _ h, fun h => by simpa using key _ _ h⟩
  · rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hz, Submodule.one_eq_span]

theorem star_det_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  set M : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) with hM
  have hd : ((LinearEquiv.det γ.1 : Eˣ) : E) = M.det := by
    rw [LinearEquiv.coe_det, hM, LinearMap.det_toMatrix']
  have hu : M.conjTranspose * M = 1 := by
    ext i j
    have h := γ.2 (Pi.single i 1) (Pi.single j 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hM, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    refine h.trans ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hd, ← Matrix.det_conjTranspose, ← Matrix.det_mul, hu, Matrix.det_one]

theorem matT_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n : ℕ}
    (x : HomE E n n) : matT e n n x = (e : E →+* E').mapMatrix (LinearMap.toMatrix' x) := rfl

variable {D : D7} {X : Fields} (s : Seam D X)

theorem detId_lat_gmap {n : ℕ} (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D L₀ (s.lat (gmap g N)) =
      Submodule.span (𝓞 D.host.E) {s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)} * TaylorLogMetric.detId D L₀ (s.lat N) := by
  have hd : s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) = (matT s.iE n n g.toLinearMap).det := by
    rw [matT_eq, ← RingHom.map_det, LinearMap.det_toMatrix', LinearEquiv.coe_det]
    rfl
  rw [hd]
  refine detId_image D L₀ _ _ _ (matT s.iE n n g.symm.toLinearMap) ?_
    ((matT_carries s.iE N (gmap g N) _).2 fun y hy => ⟨y, hy, rfl⟩) ((matT_carries s.iE (gmap g N) N _).2 ?_)
  · rw [matT_eq, matT_eq, ← map_mul, ← LinearMap.toMatrix'_comp]
    simp
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hy

theorem chi_lat_gmap (hs : s.Ok) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ} (γ : UF X.E n)
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat (gmap γ.1 N))) =
      (∏ τ, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 : star (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 := by
    rw [hst, ← hs.2, ← map_mul, star_det_mul, map_one]
  let z : unitary D.host.E := ⟨s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E), h1, by rw [mul_comm]; exact h1⟩
  have hL := sd_lat s hs hN
  rw [detId_lat_gmap, hχ.1 _ _ (norm_one_span D z.1 (by rw [← hst, mul_comm]; exact h1))
    (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (GlobalTheory.ThetaMove.Moved.sd_stdL D n) hL hL).1, hχ.2 z,
    Finset.prod_inv_distrib, ← s.iT.prod_comp]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (hs.1 τ _).symm

theorem chiLaw_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → TaylorLogMetric.IsChi D χ → (ambOf s B χ cD).ChiLaw a b := by
  intro D X s cc δ B χ cD a b hs hχ γ γ' N N' hN hN'
  change Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) =
    (∏ τ, X.embC s.σ₀ τ _) ^ _ * (∏ τ, X.embC s.σ₀ τ _) ^ _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  unfold Base.chiFac
  rw [chi_lat_gmap s hs hχ γ hN, chi_lat_gmap s hs hχ γ' hN', mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg]
  ring

end GlobalTheory.Mem.Col2.ChiFacLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
section
open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd _root_.GlobalTheory.CompactDualExists.nonempty_cdHaar

end GlobalTheory.MinfMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

def GeneratesAlong (I : W.IdealSheafData) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) : Prop :=
  (⨆ k, g ⁻¹ᵁ L.U k = ⊤) ∧ ∀ (k : L.ι) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ L.U k),
    I.ideal A = Ideal.span (Set.range fun j => (g.appLE (L.U k) A.1 h).hom ((σ j).f k))

end GlobalTheory.ProjBlowup
end
end

