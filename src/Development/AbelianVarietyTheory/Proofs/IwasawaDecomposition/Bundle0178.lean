module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceLeSpanUnitaryOrbitExtremal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm

theorem cyc_rowAct_rowAct {k n : ℕ} (g h : Matrix (Fin k) (Fin k) ℂ) (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h F) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) F := by
  have : (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.algHom_C,
      Matrix.mul_apply]
    simp only [MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    simp [MvPolynomial.C_mul, mul_assoc]
  rw [← this]; rfl

theorem cyc_rowAct_one {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin k) (Fin k) ℂ) F = F := by
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin k) (Fin k) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [this]; rfl

theorem nablaSq_le_span_unitary (n : ℕ) (mu : DomWeight n) :
    nablaSq ℂ n mu ≤ Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} := by
  have hν : Antitone mu.natW := (factNatW n mu).1
  have hmem : extremal ℂ n mu ∈ nablaSq ℂ n mu := Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW hν
  set M := Submodule.span ℂ
      {F | ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, F = Formalism.GradedWeylDivisibility.rowAct ℂ u (extremal ℂ n mu)} with hM
  have hle : M ≤ nablaSq ℂ n mu := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ _ hmem
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    intro u hu f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [cyc_rowAct_rowAct]
      exact Submodule.subset_span ⟨v * u, mul_mem hv hu, rfl⟩
    | zero => rw [map_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact M.smul_mem c hx
  have hne : M ≠ ⊥ := by
    intro e
    have h1 : extremal ℂ n mu ∈ M := Submodule.subset_span ⟨1, one_mem _, (cyc_rowAct_one _).symm⟩
    rw [e, Submodule.mem_bot] at h1
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl mu.natW h1
  exact GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl mu.natW hν M hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable M (GlobalTheory.Branching.rowAct_mem_of_unitary_stable M hU)) hne

theorem VV_le_span_vact_extremal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), VV ℂ lam ≤ Submodule.span ℂ {F | ∃ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (allPos n)) ∧ F = vact lam u (ten fun τ => extremal ℂ n (lam τ))} := by
  intro ι _ n lam
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  choose m c g hg using fun τ => Submodule.mem_span_set'.1 (nablaSq_le_span_unitary n (lam τ) (hf τ))
  choose v hv hgv using fun τ i => (g τ i).2
  have e : ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ) =
      ∑ p ∈ Fintype.piFinset (fun τ => (Finset.univ : Finset (Fin (m τ)))),
        (∏ τ, c τ (p τ)) • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ (p τ) : MvPolynomial (Fin n × Fin n) ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hg, map_sum, map_smul]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_smul]
  rw [e, SetLike.mem_coe]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  set u : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => star (v τ (p τ)) with hu
  have huU : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin n) ℂ := fun τ => Unitary.star_mem (hv τ (p τ))
  have hinv : ∀ τ, (u τ)⁻¹ = v τ (p τ) := fun τ =>
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff'.1 (hv τ (p τ)))
  have hdet : (∏ τ, (u τ).det ^ (-(lam τ).detShift)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ?_
    exact (Matrix.UnitaryGroup.det_isUnit ⟨u τ, huU τ⟩).ne_zero
  rw [← Submodule.smul_mem_iff _ hdet]
  refine Submodule.subset_span ⟨u, fun τ => ⟨huU τ, ?_⟩, ?_⟩
  · have : Formalism.REAL.Jm (allPos n) = 1 := by
      simp [Formalism.REAL.Jm, allPos]
    rw [this, mul_one, one_mul]
  · simp only [vact, ten, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n _).1, hinv, hgv]

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace GlobalTheory.DefLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Poly

variable {ι : Type} {m n : ℕ}

abbrev Pol (ι : Type) (m n : ℕ) : Type := MvPolynomial (ι × Fin m × Fin n) ℂ

def subst (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  MvPolynomial.aeval fun v => ∑ i, ∑ c, (b v.1 i v.2.1 * a v.1 v.2.2 c) • MvPolynomial.X (v.1, i, c)


open Classical in
def rowSub (n : ℕ) (τ : ι) (u : Matrix.unitaryGroup (Fin m) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun _ => 1) (fun ρ => if ρ = τ then (u : Matrix (Fin m) (Fin m) ℂ) else 1)).toLinearMap


open Classical in
def colSub (m : ℕ) (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  (subst (fun ρ => if ρ = τ then star (g : Matrix (Fin n) (Fin n) ℂ) else 1) (fun _ => 1)).toLinearMap

def rowLie (n : ℕ) (τ : ι) (k l : Fin m) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ c : Fin n, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, k, c)) ∘ₗ (MvPolynomial.pderiv (τ, l, c)).toLinearMap

def colLie (m : ℕ) (τ : ι) (k l : Fin n) : Pol ι m n →ₗ[ℂ] Pol ι m n :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, k)) ∘ₗ (MvPolynomial.pderiv (τ, i, l)).toLinearMap

theorem rowLie_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowLie n τ k l P = ∑ c : Fin n, MvPolynomial.X (τ, k, c) * MvPolynomial.pderiv (τ, l, c) P := by
  simp [rowLie, LinearMap.sum_apply]

theorem colLie_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) :
    colLie m τ k l P = ∑ i : Fin m, MvPolynomial.X (τ, i, k) * MvPolynomial.pderiv (τ, i, l) P := by
  simp [colLie, LinearMap.sum_apply]

end Poly

def IrrFam {ι κ X : Type} [AddCommGroup X] [Module ℂ X] (π : ι → κ → Module.End ℂ X) : Prop :=
  ∀ U : Submodule ℂ X, (∀ τ u, ∀ x ∈ U, π τ u x ∈ U) → U = ⊥ ∨ U = ⊤

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def AllPlus (M : DSModel V S) : Prop := ∀ τ a, M.ε τ a = true

def unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (M.fr τ)⁻¹ * u * M.fr τ

def IsTensAct (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) : Prop :=
  ∀ τ u x, inclT M (π τ u x) = actT M τ (unfr M τ u) (inclT M x)

variable {M : DSModel V S}

theorem AllPlus.jm (h : AllPlus M) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = 1 := by
  unfold Formalism.REAL.Jm
  simp [h τ]

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem AllPlus.gram (h : AllPlus M) (τ : D.what₂.Tau) : gramAt D V τ = (M.fr τ)ᴴ * M.fr τ := by
  rw [← M.fr_gram τ, h.jm, Matrix.mul_one]

theorem AllPlus.posDef (h : AllPlus M) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  rw [h.gram]
  exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 (M.fr_unit τ))

theorem AllPlus.cart (h : AllPlus M) (τ : D.what₂.Tau) : cart M τ = 1 := by
  unfold Links.cart
  rw [h.jm, Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem fr_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.fr τ * unfr M τ u * (M.fr τ)⁻¹ = u := by
  unfold unfr
  rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ),
    Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M τ)]

theorem rep_unfr (M : DSModel V S) (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    M.rep τ (unfr M τ u) = M.σ τ u := by
  unfold DSModel.rep
  rw [fr_unfr]

theorem AllPlus.unfr_mem (h : AllPlus M) (τ : D.what₂.Tau) (u : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    unfr M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have hu : (u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  have e : M.fr τ * unfr M τ u = u * M.fr τ := by
    unfold unfr
    rw [Matrix.mul_assoc (M.fr τ)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (fr_det M τ)]
  show (unfr M τ u)ᴴ * gramAt D V τ * unfr M τ u = gramAt D V τ
  rw [h.gram]
  calc _ = (M.fr τ * unfr M τ u)ᴴ * (M.fr τ * unfr M τ u) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((u : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * u) * M.fr τ := by
      rw [e]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.mul_one]

theorem AllPlus.exists_unfr (h : AllPlus M) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : ∃ u : Matrix.unitaryGroup (Fin V.rank) ℂ, unfr M τ u = g := by
  have hg' : gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g = (M.fr τ)ᴴ * M.fr τ := by rw [← h.gram]; exact hg
  refine ⟨⟨M.fr τ * g * (M.fr τ)⁻¹, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, ?_⟩
  · calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ (fr_det M τ)]; simp
  · show (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ = g
    rw [Matrix.mul_assoc (M.fr τ), Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ),
      Matrix.nonsing_inv_mul_cancel_right _ _ (fr_det M τ)]

end Model

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem colNorm_exists_im_ne_zero {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h a)

theorem colNorm_normAt_column (D : D7) (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  rw [D.nuIn_norm, normAt_sq_eq_majAt_re, (D.fm u).emb_norm, ← D.nuIn_jN, norm_eq_sqrt_re_inner (𝕜 := ℂ), D.eMu_isom]
  rfl

theorem colNorm_of_nuTie : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), R.NuTie → M.ColNorm := by
  intro D Bs A X fc s R cr M h u
  obtain ⟨L, hL⟩ := h u
  refine ⟨1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a = cj s (D.what₂.embLL a) := by
    rw [← R.v0]; exact R.twist
  have := fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL s htw (colNorm_exists_im_ne_zero _) (D.div.Nu u) _ L _ (R.eNu u) hL
    (D.what₂.Mu u) (D.jN u) (M.cφ u) (colNorm_normAt_column D u) (M.cφ_eq u) φ
  rw [← R.v0] at this
  exact this

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocWeil.CompactPart

variable {D : D7}

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem infMat_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V} (hk : k ∈ GfC V) :
    infMat D.sp.cm.sig V.gram θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.LocWeil.CompactPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownwardLevelMoveReachesKernelLattice
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

theorem pairOf_act_of_agree {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M N : Submodule R V)
    (pr : M →+ W) (pr' : N →+ W') (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z) (φ : Module.Dual k W) (g : Module.Dual k W') (e : V ≃ₗ[R] V)
    (hL : loc res (M.map (e : V →ₗ[R] V)) = loc res N)
    (hf : ∀ (x : M) (hx : e x.1 ∈ N), φ (pr x) = g (pr' ⟨_, hx⟩)) :
    ((pairOf res M pr φ).act e).L = loc res N ∧
      ∀ x ∈ loc res N, ((pairOf res M pr φ).act e).f x = g (locExt res N pr' x) := by
  have hmem : ∀ x, e.symm x ∈ loc res M ↔ x ∈ loc res N := by
    intro x
    rw [← hL, mem_loc, mem_loc]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [Submodule.mem_map_equiv, map_smul]
  refine ⟨Submodule.ext fun x => (Pr.mem_act e _ x).trans (hmem x), fun x hx => ?_⟩
  have hx' := (hmem x).2 hx
  obtain ⟨s, hs0, h1⟩ := (mem_loc res M _).1 hx'
  obtain ⟨s', hs0', h2⟩ := (mem_loc res N _).1 hx
  have h1' : (s' * s) • e.symm x ∈ M := by rw [mul_smul]; exact M.smul_mem _ h1
  have h2' : (s' * s) • x ∈ N := by rw [mul_comm, mul_smul]; exact N.smul_mem _ h2
  have hne : res (s' * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hs0' hs0
  have he : e ((s' * s) • e.symm x) = (s' * s) • x := by rw [map_smul, e.apply_symm_apply]
  have h3 := hf ⟨_, h1'⟩ (by rw [he]; exact h2')
  have h4 : pr' ⟨e ((s' * s) • e.symm x), by rw [he]; exact h2'⟩ = pr' ⟨_, h2'⟩ := by
    congr 1; exact Subtype.ext he
  rw [h4, locExt_spec res M pr hs _ hx' _ h1', locExt_spec res N pr' hs' _ hx _ h2', map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at h3
  exact mul_left_cancel₀ hne h3

theorem pc_act_down : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  intro D u A i hi P K v c c' g γ hL hf
  refine pairOf_act_of_agree (A.res v) _ _ (P.pr v c') (P.prk v c) (P.pr_smul v c') (P.prk_smul v c) _ g (glE γ) ?_ hf
  rw [map_glE, hL, _root_.GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c]

end GlobalTheory.LevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RootUnip

open GlobalTheory.BesselCompare (hA_add hA_smul hA_smul_right)

variable {D : D7} {B : HSp D}

def kMat (B : HSp D) (v y : Fin B.rank → AE D) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  1 + vecMulVec v ((fun i => cA D (y i)) ᵥ* B.gram.map (incA D)) -
    vecMulVec y ((fun i => cA D (v i)) ᵥ* B.gram.map (incA D))

theorem kMat_mulVec (v y x : Fin B.rank → AE D) :
    (kMat B v y).mulVec x = x + hA B x y • v - hA B x v • y := by
  rw [kMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, hA_eq, hA_eq, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [op_smul_eq_smul]

theorem continuous_rankTwo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    {c : R → R} (hc : Continuous c) (J : Matrix (Fin n) (Fin n) R) (v w : Fin n → R) :
    Continuous fun y : Fin n → R => 1 + vecMulVec v ((fun i => c (y i)) ᵥ* J) - vecMulVec y w := by
  have hc' : Continuous fun y : Fin n → R => fun i => c (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  have h1 := continuous_const (y := v).matrix_vecMulVec (hc'.matrix_vecMul (continuous_const (y := J)))
  have h2 := (continuous_id (X := Fin n → R)).matrix_vecMulVec (continuous_const (y := w))
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (continuous_const.add (h1.matrix_elem i j)).sub (h2.matrix_elem i j)

theorem continuous_kMat (v : Fin B.rank → AE D) : Continuous (kMat B v) :=
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  continuous_rankTwo GlobalTheory.FockCompare.ThetaCont.continuous_conj _ _ _

section

variable {η : AE D} (hη : η * cA D η = 0) {v y : Fin B.rank → AE D} (hy : η • y = y) (hv : hA B v y = 0)

include hη hy in
theorem hA_smul_self (x : Fin B.rank → AE D) : hA B x y • y = 0 := by
  have e : hA B x y = cA D η * hA B x y := by rw [← hA_smul_right, hy]
  rw [e, ← hy, smul_smul, hy, mul_assoc, mul_comm (hA B x y), ← mul_assoc, mul_comm (cA D η), hη, zero_mul,
    zero_smul]

include hη hy in
theorem hA_mul_hA (x x' : Fin B.rank → AE D) : hA B x y * hA B y x' = 0 := by
  rw [← hA_smul, hA_smul_self hη hy, hA_zero]

include hη hy in
theorem hA_self : hA B y y = 0 := by
  have e : hA B y y = η * (cA D η * hA B y y) := by rw [← hA_smul_right, ← hA_smul, hy]
  rw [e, ← mul_assoc, hη, zero_mul]

include hv in
theorem hA_yv : hA B y v = 0 := by rw [← hA_herm, hv, map_zero]

include hη hy hv in
theorem kMat_neg_mul : kMat B v (-y) * kMat B v y = 1 := by
  refine Matrix.mulVec_injective (funext fun x => ?_)
  show (kMat B v (-y) * kMat B v y).mulVec x = (1 : Matrix _ _ _).mulVec x
  rw [← Matrix.mulVec_mulVec, kMat_mulVec, kMat_mulVec, Matrix.one_mulVec, hA_neg_right]
  simp only [hA_sub, hA_add, hA_smul, hv, hA_yv hv, hA_self hη hy, mul_zero, add_zero, sub_zero]
  have h0 : (hA B x y * hA B v v) • y = 0 := by
    rw [mul_comm, mul_smul, hA_smul_self hη hy, smul_zero]
  rw [smul_neg, add_smul, h0, neg_smul]
  abel

include hη hy hv in
theorem kMat_mul_neg : kMat B v y * kMat B v (-y) = 1 := by
  have := kMat_neg_mul (y := -y) (v := v) hη (by rw [smul_neg, hy]) (by rw [hA_neg_right, hv, neg_zero])
  rwa [neg_neg] at this

include hη hy hv in
theorem hA_kMat (x x' : Fin B.rank → AE D) :
    hA B ((kMat B v y).mulVec x) ((kMat B v y).mulVec x') = hA B x x' := by
  rw [kMat_mulVec, kMat_mulVec]
  simp only [hA_sub, hA_add, hA_smul, hA_sub_right, hA_add_right, hA_smul_right, hA_herm, hv, hA_yv hv,
    hA_self hη hy]
  linear_combination hA B v v * hA_mul_hA hη hy x x'

end

theorem unitary_of_hA {M : Matrix (Fin B.rank) (Fin B.rank) (AE D)}
    (h : ∀ x y, hA B (M.mulVec x) (M.mulVec y) = hA B x y) :
    (M.map (cA D))ᵀ * B.gram.map (incA D) * M = B.gram.map (incA D) := by
  have key : ∀ x y : Fin B.rank → AE D,
      (fun i => cA D (y i)) ⬝ᵥ ((M.map (cA D))ᵀ * B.gram.map (incA D) * M).mulVec x =
        (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := fun x y => by
    have e : (fun i => cA D (M.mulVec y i)) = (M.map (cA D)).mulVec fun i => cA D (y i) :=
      funext fun i => RingHom.map_mulVec (cA D) _ y i
    have := h x y
    rwa [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at this
  refine Matrix.mulVec_injective (funext fun x => funext fun i => ?_)
  have := key x (Pi.single i 1)
  rwa [show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct, single_one_dotProduct] at this

theorem exists_continuous_isK (D : D7) (B : HSp D) (η : AE D) (hη : η * cA D η = 0) (v : Fin B.rank → AE D) :
    ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B,
      Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  refine ⟨fun y => ⟨⟨kMat B v y.1, kMat B v (-y.1), kMat_mul_neg hη y.2.1 y.2.2, kMat_neg_mul hη y.2.1 y.2.2⟩,
    unitary_of_hA (hA_kMat hη y.2.1 y.2.2)⟩, ?_, fun y x => kMat_mulVec v y.1 x⟩
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_kMat v).comp continuous_subtype_val
  · exact (continuous_kMat v).comp continuous_subtype_val.neg

end GlobalTheory.RootUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVectorStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_theorem_adelic_one_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  first | exact @GlobalTheory.AdelicWitt.witt_adelic | exact GlobalTheory.AdelicWitt.witt_adelic | (intros; apply GlobalTheory.AdelicWitt.witt_adelic <;> assumption)
end

