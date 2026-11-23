module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLintegralEqOfMeasurable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemColumnLevelIffMemLinkedFrameLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.FibreUnitri
open Matrix

section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E)

theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gramR_comb {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (X : Fin a → Fin M → R ⊗[F] E) :
    gramR R σ J (fun b => ∑ c, u c b • X c) = (u.map (sigR R σ)).transpose * gramR R σ J X * u := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, d, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, d]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

def cgr {a : ℕ} (m A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) : Matrix (Fin a) (Fin a) (R ⊗[F] E) :=
  (m.map (sigR R σ)).transpose * A * m

theorem cgr_cgr {a : ℕ} (u w A : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (huw : u * w = 1) :
    cgr R σ w (cgr R σ u A) = A := by
  have e1 : (w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, huw,
      map_one, Matrix.transpose_one]
  unfold cgr
  calc (w.map (sigR R σ)).transpose * ((u.map (sigR R σ)).transpose * A * u) * w
      = ((w.map (sigR R σ)).transpose * (u.map (sigR R σ)).transpose) * A * (u * w) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [e1, huw, Matrix.one_mul, Matrix.mul_one]

theorem cgr_mem (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E))
    (S : HermR R σ a) : cgr R σ m (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) ∈ HermR R σ a := by
  have hS : ∀ p q, sigR R σ ((S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) q p) =
      (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) p q := S.2
  intro p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cgr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    sigR_invol R σ hσ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hS]
  ring

def cgrH (hσ : ∀ x, σ (σ x) = x) {a : ℕ} (m : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (S : HermR R σ a) :
    HermR R σ a :=
  ⟨cgr R σ m S, cgr_mem R σ hσ m S⟩

theorem comb_comb {M a : ℕ} (u w : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ c, w c b • ∑ d, u d c • X d) = fun b => ∑ d, (u * w) d b • X d := by
  funext b
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem comb_one {M a : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    (fun b => ∑ d, (1 : Matrix (Fin a) (Fin a) (R ⊗[F] E)) d b • X d) = X := by
  funext b
  simp [Matrix.one_apply]

theorem linIndep_comb {M a : ℕ} (m m' : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (h : m' * m = 1)
    (X : Fin a → Fin M → R ⊗[F] E) (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (fun b => ∑ c, m c b • X c) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg
  have h0 : ∑ c, (m *ᵥ g) c • X c = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
  have hv : m *ᵥ g = 0 := funext (hX _ h0)
  have : g = m' *ᵥ (m *ᵥ g) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  intro i
  rw [this, hv, Matrix.mulVec_zero]
  rfl

end Alg

section Abstract

variable {V Y X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem isFibreFamily_transport (e : V ≃ₜ V) (r : X ≃ₜ X) {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} {ν : Measure X} {fib : X → Measure V} (hfib : IsFibreFamily μ f ι U ν Set.univ fib)
    (hμ : μ.map e.toMeasurableEquiv = μ) (hν : ν.map r.toMeasurableEquiv = ν)
    (hf : ∀ x b, f (e x) = ι (r b) ↔ f x = ι b) (hU : e ⁻¹' U = U) :
    IsFibreFamily μ f ι U ν Set.univ
      (fun b => (fib (r.symm b)).map e.toMeasurableEquiv) := by
  set em := e.toMeasurableEquiv with hem
  set rm := r.toMeasurableEquiv with hrm
  have hU' : em ⁻¹' U = U := hU
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs hts => ?_⟩
  · rw [MeasurableEquiv.map_apply]
    have : em ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι (r.symm b)} ∩ U)ᶜ := by
      ext x
      have hx : e x ∈ U ↔ x ∈ U := Set.ext_iff.1 hU x
      have hb := hf x (r.symm b)
      rw [r.apply_symm_apply] at hb
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
      change ¬ (f (e x) = ι b ∧ e x ∈ U) ↔ ¬ (f x = ι (r.symm b) ∧ x ∈ U)
      rw [hb, hx]
    rw [this]
    exact hfib.1 _
  · have key : ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x in U, φ x ∂μ := by
      calc ∫⁻ x in U, φ (em x) ∂μ = ∫⁻ x, φ (em x) ∂(μ.restrict (em ⁻¹' U)) := by rw [hU']
        _ = ∫⁻ x, φ x ∂((μ.restrict (em ⁻¹' U)).map em) := (lintegral_map_equiv _ _).symm
        _ = ∫⁻ x, φ x ∂((μ.map em).restrict U) := by rw [MeasurableEquiv.restrict_map]
        _ = ∫⁻ x in U, φ x ∂μ := by rw [hμ]
    rw [← key, hfib.2.1 (fun x => φ (em x)) (hφ.comp em.measurable)]
    have h2 : ∀ c, ∫⁻ x, φ (em x) ∂(fib c) = ∫⁻ x, φ x ∂((fib (r.symm (rm c))).map em) := by
      intro c
      rw [lintegral_map_equiv]
      change _ = ∫⁻ x, φ (em x) ∂(fib (r.symm (r c)))
      rw [r.symm_apply_apply]
    simp_rw [h2]
    conv_rhs => rw [← hν]
    exact (lintegral_map_equiv (fun b => ∫⁻ x, φ x ∂((fib (r.symm b)).map em)) rm).symm
  · have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨h1, h2⟩ := hfib.2.2 (φ ∘ e) (hc.comp e.continuous) (hcs.comp_homeomorph e) hts'
    refine ⟨fun b _ => (integrable_map_equiv em φ).2 (h1 _ (Set.mem_univ _)), ?_⟩
    have e2 : (fun b => ∫ x, φ x ∂((fib (r.symm b)).map em)) =
        (fun c => ∫ x, (φ ∘ e) x ∂(fib c)) ∘ r.symm :=
      funext fun b => integral_map_equiv _ _
    rw [e2]
    have h3 : Continuous fun c => ∫ x, (φ ∘ e) x ∂(fib c) := continuousOn_univ.1 h2
    exact (h3.comp r.symm.continuous).continuousOn

end Abstract
end GlobalTheory.FibreUnitri

namespace GlobalTheory.FibreUnitri
open Matrix

theorem fibre_unitri_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib hfib S u hdiag htri hS
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  obtain ⟨hring, -, -, hsc, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hE n J hJ v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩

  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => htri i j hij)]
    simp [hdiag]
  have hu : IsUnit u.det := by rw [hdet]; exact isUnit_one
  set w := u⁻¹ with hw
  have huw : u * w = 1 := Matrix.mul_nonsing_inv u hu
  have hwu : w * u = 1 := Matrix.nonsing_inv_mul u hu

  have hcont : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E),
      Continuous (fun (X : Fin a → Fin n → Fv F v ⊗[F] E) b => ∑ c, m c b • X c) := by
    intro m
    refine continuous_pi fun b => continuous_finsetSum _ fun c _ => ?_
    exact (continuous_apply c).const_smul (m c b)
  let e : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X b => ∑ c, u c b • X c
      invFun := fun X b => ∑ c, w c b • X c
      left_inv := fun X => by
        show (fun b => ∑ c, w c b • ∑ d, u d c • X d) = X
        rw [comb_comb, huw, comb_one]
      right_inv := fun X => by
        show (fun b => ∑ c, u c b • ∑ d, w d c • X d) = X
        rw [comb_comb, hwu, comb_one]
      continuous_toFun := hcont u
      continuous_invFun := hcont w }

  have hcontH : ∀ m : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), Continuous (cgrH (Fv F v) σ hσ m) := by
    intro m
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let r : HermR (Fv F v) σ a ≃ₜ HermR (Fv F v) σ a :=
    { toFun := cgrH (Fv F v) σ hσ u
      invFun := cgrH (Fv F v) σ hσ w
      left_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ u w _ huw)
      right_inv := fun T => Subtype.ext (cgr_cgr (Fv F v) σ w u _ hwu)
      continuous_toFun := hcontH u
      continuous_invFun := hcontH w }
  obtain ⟨hμu, hνu⟩ := _root_.GlobalTheory.UnitriTuple.unitri_haar F E σ hE n J hJ v a u hdiag htri
  have hμe : μ.map e.toMeasurableEquiv = μ := hμu μ hμ
  have hνr : ν.map r.toMeasurableEquiv = ν := hνu ν hν r (fun T => rfl)
  have hf : ∀ X T, gramR (Fv F v) σ J (e X) = ((r T : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ↔
      gramR (Fv F v) σ J X = (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := by
    intro X T
    have h1 : gramR (Fv F v) σ J (e X) = cgr (Fv F v) σ u (gramR (Fv F v) σ J X) :=
      gramR_comb (Fv F v) σ J u X
    have h2 : ((r T : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
        cgr (Fv F v) σ u T := rfl
    rw [h1, h2]
    constructor
    · intro h
      have := congrArg (cgr (Fv F v) σ w) h
      rwa [cgr_cgr _ _ _ _ _ huw, cgr_cgr _ _ _ _ _ huw] at this
    · intro h
      rw [h]
  have hU : e ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    constructor
    · intro h
      have h' := linIndep_comb (Fv F v) w u huw _ h
      have e2 : (fun b => ∑ c, w c b • (e X) c) = X := e.left_inv X
      rw [e2] at h'
      exact h'
    · intro h
      exact linIndep_comb (Fv F v) u w hwu X h
  have hfam := isFibreFamily_transport e r hfib hμe hνr hf hU
  have heq := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hE n J hJ v a μ ν hμ hν fib hfib _ hfam
  have hrS : r.symm S = S := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hS.symm
  have := congrFun heq S
  simp only [hrS] at this
  exact this.symm

end GlobalTheory.FibreUnitri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStabiliserFromAdaptedPair
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem onto_gmap_mul (a b : GV D) (M : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem onto_gmap_one (M : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) M = M := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem onto_side {T : D.host.E} {A B : LFlag (D.sp.Y 0) D.R.rS T} {M : LV D} {G h : GV D}
    (hG : Adapt G A B) (hh : Adapt h B B)
    (hL : Lsub (Formalism.HermitianLatticesTheory.gmap h (Formalism.HermitianLatticesTheory.gmap G M)) B = Lsub (Formalism.HermitianLatticesTheory.gmap G M) B)
    (hs : ∀ σ, Adapt σ A A → Lsub (Formalism.HermitianLatticesTheory.gmap σ M) A = Lsub M A →
      ∃ n ∈ NRat A, Formalism.HermitianLatticesTheory.gmap (n * σ) M = M) :
    ∃ n ∈ NRat A, n * (G⁻¹ * h * G) ∈ Aut0 A M ∧
      ∀ x ∈ orth (VS D) (Xsp B), h x - (G * (n * (G⁻¹ * h * G)) * G⁻¹) x ∈ Xsp B := by
  have hGi : Adapt G⁻¹ B A := adapt_inv hG
  have hσ : Adapt (G⁻¹ * h * G) A A := by
    have h2 : Adapt (G⁻¹ * (h * G)) A A := adapt_mul (adapt_mul hG hh) hGi
    rwa [mul_assoc]
  have hGiso : G ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hG.1
  have hmap : (Xsp A).map (G : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := adapt_xsp hG

  have hinj : ∀ X Y : LV D, Formalism.HermitianLatticesTheory.gmap G X = Formalism.HermitianLatticesTheory.gmap G Y → X = Y := by
    intro X Y hXY
    have hXY' := congrArg (Formalism.HermitianLatticesTheory.gmap G⁻¹) hXY
    rwa [← onto_gmap_mul, ← onto_gmap_mul, inv_mul_cancel, onto_gmap_one, onto_gmap_one] at hXY'
  have e : G * (G⁻¹ * h * G) = h * G := by group
  have hLσ : Lsub (Formalism.HermitianLatticesTheory.gmap (G⁻¹ * h * G) M) A = Lsub M A := by
    apply hinj
    rw [← lsub_gmap_of_map_Xsp_eq D T A B G _ hGiso hmap, ← lsub_gmap_of_map_Xsp_eq D T A B G M hGiso hmap,
      ← onto_gmap_mul, e, onto_gmap_mul]
    exact hL
  obtain ⟨n, hn, hnM⟩ := hs _ hσ hLσ
  refine ⟨n, hn, ?_, ?_⟩
  · have hA : Adapt (n * (G⁻¹ * h * G)) A A := adapt_mul hσ (adapt_nrat hn)
    show Adapt _ A A ∧ Formalism.HermitianLatticesTheory.gmap _ M = M
    exact ⟨hA, hnM⟩
  · intro x hx

    obtain ⟨-, -, hm3⟩ := nrat_conj hG hn
    have hhx : h x ∈ orth (VS D) (Xsp B) := mem_of_map_eq (adapt_orth hh) hx
    have e' : G * (n * (G⁻¹ * h * G)) * G⁻¹ = G * n * G⁻¹ * h := by group
    rw [e']
    show h x - (G * n * G⁻¹) (h x) ∈ Xsp B
    rw [← neg_sub]
    exact neg_mem (hm3 (h x) hhx)

theorem stab_onto : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' Λ : LV D) (γ g h : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → (∀ σ, Adapt σ F0 F0 → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam) F0 = Lsub lam F0 → ∃ n ∈ NRat F0, Formalism.HermitianLatticesTheory.gmap (n * σ) lam = lam) → (∀ σ, Adapt σ F0' F0' → Lsub (Formalism.HermitianLatticesTheory.gmap σ lam') F0' = Lsub lam' F0' → ∃ n ∈ NRat F0', Formalism.HermitianLatticesTheory.gmap (n * σ) lam' = lam') → h ∈ stabL F F' Λ → ∃ b, GlobalTheory.StabCnt.InB F0 F0' lam lam' γ b ∧ GlobalTheory.StabCnt.Corr F0 F F0' F' γ g b h := by
  intro D T T' F0 F F0' F' lam lam' Λ γ g h hγ hlam hg hg' hΛ hs hs' hstab
  obtain ⟨hH0, hdat⟩ := hstab
  have hL1 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F = Lsub Λ F := congrArg Prod.fst hdat
  have hL2 : Lsub (Formalism.HermitianLatticesTheory.gmap h Λ) F' = Lsub Λ F' := congrArg (fun p => p.2.1) hdat
  obtain ⟨hhF, hhF'⟩ := frameAdaptedIsometry_of_fixing_both_frames hH0
  have hgγ : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have e2 : Formalism.HermitianLatticesTheory.gmap (g * γ) lam' = Λ := by rw [onto_gmap_mul, hlam, hΛ]
  obtain ⟨n, hn, hb1, hx1⟩ := onto_side (M := lam) hg hhF (by rw [← hΛ]; exact hL1) hs
  obtain ⟨n', hn', hb2, hx2⟩ := onto_side (M := lam') hgγ hhF' (by rw [e2]; exact hL2) hs'

  have key : n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹ = n * γ * n'⁻¹ := by group
  have e3 : g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹ =
      g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * (g * γ)⁻¹ := by group
  have hx2' : ∀ x ∈ orth (VS D) (Xsp F'),
      h x - (g * γ * (n' * ((g * γ)⁻¹ * h * (g * γ))) * γ⁻¹ * g⁻¹) x ∈ Xsp F' := by
    rw [e3]; exact hx2
  have hI := (_root_.GlobalTheory.GdatIota.gdat_iff_iotaCompat D T T' F0 F F0' F' lam lam' Λ γ g h (n * (g⁻¹ * h * g))
    (n' * ((g * γ)⁻¹ * h * (g * γ))) hγ hlam hg hg' hΛ hb1 hb2 hH0 hx1 hx2').mp hdat
  have e4 : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) = 1 := by group
  have hF : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F := by rw [e4]; exact nrat_one F
  have hF' : h⁻¹ * (g * n⁻¹ * (n * (g⁻¹ * h * g)) * g⁻¹) ∈ NRat F' := by rw [e4]; exact nrat_one F'
  have hKey : KeyEq F0 F0' lam γ (n * (g⁻¹ * h * g) * γ * (n' * ((g * γ)⁻¹ * h * (g * γ)))⁻¹) :=
    ⟨⟨n, hn, n'⁻¹, nrat_inv hn', key⟩, hI⟩
  refine ⟨(n * (g⁻¹ * h * g), n' * ((g * γ)⁻¹ * h * (g * γ))), ?_, ?_⟩
  · exact ⟨hb1, hb2, hKey⟩
  · exact ⟨hH0, n, hn, n'⁻¹, nrat_inv hn', key, hF, hF'⟩

end GlobalTheory.StabCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IwasawaShape

theorem gauge_ne_zero_finite {n : ℕ} {ε : Fin n → Bool} (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) : μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ := by
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hr0, hrt⟩ := (hpos.and ((hlim.eventually_ne hL0).and (hlim.eventually_ne hLt))).exists
  set B : Set (Formalism.REAL.UJ ε) := {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} with hB
  have hden0 : ENNReal.ofReal (r ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hr d
  have hB0 : μ B ≠ 0 := by
    intro h; apply hr0; rw [h, ENNReal.zero_div]
  have hBt : μ B ≠ ⊤ := by
    intro h; apply hrt; rw [h]; exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
  have hf : Continuous fun g : Formalism.REAL.UJ ε => Real.sqrt (Formalism.REAL.hs (uMat g - 1)) := by
    refine Real.continuous_sqrt.comp ?_
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    refine (Continuous.norm ?_).pow 2
    exact (continuous_apply k).comp ((continuous_apply i).comp
      (GlobalTheory.FlagLeviGroup.continuous_uMat.sub continuous_const))
  have hBm : MeasurableSet B := (isClosed_le hf continuous_const).measurableSet
  have hBn : B ∈ nhds (1 : Formalism.REAL.UJ ε) := by
    have hO : IsOpen {g : Formalism.REAL.UJ ε | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < r} :=
      isOpen_lt hf continuous_const
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => by
      rw [hB, Set.mem_ofPred_eq]; rw [Set.mem_ofPred_eq] at hg; exact hg.le
    show Real.sqrt (Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r
    rw [GlobalTheory.FlagLeviGroup.uMat_one, sub_self]
    unfold Formalism.REAL.hs
    simpa using hr
  refine ⟨fun h => hB0 (by rw [h]; rfl), ?_⟩
  exact finiteOnCompacts_of_nhds M μ h0 hM (fun s hs => hinv s hs) B hBm hBn hBt

theorem coe_KG {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) = maxK ε := by
  ext g
  have hJ := GlobalTheory.RealIwasawa.uMat_form g
  change g ∈ Formalism.REAL.KG ε ↔ (uMat g)ᴴ * uMat g = 1
  rw [Formalism.REAL.mem_KG]
  change (uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g) ↔ _
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have h' : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hJ]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h', Matrix.one_mul]

theorem iwasawa_shape : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  intro n ε p q _ _ a j hj W hW μN μM μK hN hM hK0 hK1 hKi
  obtain ⟨⟨N, hNs⟩, hNc, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε a j W hW
  obtain ⟨⟨M, hMs⟩, hMc, ⟨K, hKs⟩, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε a W
  obtain ⟨hdec, huniq⟩ := GlobalTheory.RealIwasawa.iwasawa n ε a j W hW
  have eN : ∀ x, x ∈ N ↔ x ∈ flagN ε W := fun x => by rw [← hNs]; rfl
  have eM : ∀ x, x ∈ M ↔ x ∈ flagM ε W := fun x => by rw [← hMs]; rfl
  have eK : ∀ x, x ∈ K ↔ x ∈ maxK ε := fun x => by rw [← hKs]; rfl
  have hKc : IsCompact (K : Set (Formalism.REAL.UJ ε)) := by
    rw [hKs, ← coe_KG]
    exact isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) (dimN n j) μN := by rw [hNs]; exact hN
  have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [hMs]; exact hM
  have hNc' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := by rw [hNs]; exact hNc
  have hMc' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := by rw [hMs]; exact hMc
  obtain ⟨hN0, hNf⟩ := gauge_ne_zero_finite N _ μN hNc' hN'
  obtain ⟨hM0, hMf⟩ := gauge_ne_zero_finite M _ μM hMc' hM'
  have := hNf
  have := hMf
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε a j W hj hW μN hN
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.IwasawaShape.exists_lintegral_eq N M K hNc' hMc' hKc
    (fun m hm u hu => (eN _).2 (hnorm m ((eM m).1 hm) u ((eN u).1 hu)))
    (fun u hu m hm hk => huniq u ((eN u).1 hu) m ((eM m).1 hm) ((eK _).1 hk))
    (fun g => by
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g
      exact ⟨u, (eN u).2 hu, m, (eM m).2 hm, k, (eK k).2 hk, rfl⟩)
    (Formalism.REAL.muG ε) μN μM μK (NeZero.ne _) hN0 hM0 hN'.1 hM'.1
    (fun s hs => hN'.2.1 s hs) (fun s hs => hM'.2.1 s hs) (fun s hs => hKi s ((eK s).1 hs))
    (fun m => ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id))
    (fun m hm => hmod m ((eM m).1 hm))
  exact ⟨c, hc0, hct, hc⟩

end GlobalTheory.IwasawaShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelConjHolds
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem levelConj_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), LevelConj D F := by
  intro D F X hK u wt ιA h0 hW hI hL
  obtain ⟨Fr, hFr⟩ := _root_.GlobalTheory.St.G.FrameLink.frame_exists D X u wt ιA hW hI
  obtain ⟨hMq, -, -, -, -, -⟩ := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hI
  obtain ⟨hT, hg, hTg, hf, hNk, hH, hdet⟩ := record_facts D u
  have hΛ : ∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat D.host.F (F u).cls0.lev.Lb ↔ x ∈ hat D.host.F (Mq wt) := by
    intro x
    rw [hMq x]
    exact hL x
  obtain ⟨h1, hL1, hK1⟩ := _root_.GlobalTheory.St.G.level_char_match D.host.F D.host.E D.sp.cm (D.R.N 0) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) hH hdet
    (D.mem u).A.T D.R.f D.R.t D.R.k D.R.k D.R.k (D.R.N 0) D.host.g (F u).cls0.lev (F u).gl (F u).glev0
    hNk.symm hNk.symm hNk.symm rfl (D.mem u).A.T_prime D.host.g_prime D.host.g_ne hTg hg hT hf
    (hat D.host.F (Mq wt)) Fr h0 hΛ
  refine ⟨h1, fun x => ?_, fun h y hy => ?_⟩
  · exact (hL1 x).trans (hMq x)
  · have hin := _root_.GlobalTheory.St.G.ColLevel.level_link D X u wt ιA hW hI hK Fr hFr h y hy
    have hch := _root_.GlobalTheory.St.G.ColChar.psiK_eq_chi D X u wt ιA hW hI hK Fr hFr h y hy
    refine ⟨hin.trans (hK1 y).1, fun hk hy' => ?_⟩
    rw [hch hk]
    exact (hK1 y).2 hy'

end GlobalTheory.St.G
end

