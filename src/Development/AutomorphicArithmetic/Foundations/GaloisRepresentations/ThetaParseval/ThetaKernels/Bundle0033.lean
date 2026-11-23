module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.ThetaSumAdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.ContinuousMkG
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainLin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem rho_add_k (w) (Φ Φ' : d.Fn) : d.dd.rho d.B.ψ w (Φ + Φ') = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Φ' := by
  funext y
  simp [Darboux.rho, schr, mul_add]
theorem rho_smul_k (w) (a : ℂ) (Φ : d.Fn) : d.dd.rho d.B.ψ w (a • Φ) = a • d.dd.rho d.B.ψ w Φ := by
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
def Tl_k : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Φ' := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_add_k, map_add (f := _)]
  map_smul' a Φ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_smul_k, map_smul, RingHom.id_apply]
theorem Tl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_k d Φ = d.T Φ := rfl
def secl_k : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' Φ Φ' := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.add_apply, map_add (f := _)]
  map_smul' a Φ := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]
theorem secl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d Φ = d.sec0 Φ := rfl
theorem om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem S_mem_k (g) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch :=
  d.ok.dbl.lin.pres g Φ h
theorem thetaSum_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    thetaSum F (Φ + Φ') = thetaSum F Φ + thetaSum F Φ' := by
  have h1 := (hT F E σ d Φ h).1
  have h2 := (hT F E σ d Φ' h').1
  have h3 := (hT F E σ d (Φ + Φ') (d.sch.add_mem h h')).1
  have h4 := h1.add h2
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_add (f := _), Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem thetaSum_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : thetaSum F (a • Φ) = a * thetaSum F Φ := by
  have h1 := (hT F E σ d Φ h).1
  have h3 := (hT F E σ d (a • Φ) (d.sch.smul_mem a h)).1
  have h4 := h1.mul_left a
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem I_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have i1 := ((hA F E σ d).2.2 Φ h).1 x
  have i2 := ((hA F E σ d).2.2 Φ' h').1 x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) = thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) :=
    fun g => by
      rw [map_add (f := _), map_add (f := _)]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_add_k d hT (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h)) (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add i1 i2, smul_add]
theorem I_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) :=
    fun g => by
      rw [map_smul, map_smul]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_smul_k d hT a (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]
theorem I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (f : ι → d.Fn) (h : ∀ i ∈ s, f i ∈ d.sch) :
    d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hT 0 (d.sch.zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hT hA (h a (Finset.mem_insert_self _ _)) (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDSt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
def EpsEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    (d.A.IsHerm σ d.B d.r d.s ∧ ε = -1 ∨ d.A.IsSkew σ d.B d.r d.s ∧ ε = 1)
def FrEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (d.A.IsHerm σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, (1 : ℂ) • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1) ∧
  (d.A.IsSkew σ d.B d.r d.s → ∃ (fr : InfinitePlace F → GL (Fin d.m) ℂ) (sg : InfinitePlace F → ℤˣ),
    ∀ w, Complex.I • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1)
def IotaEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  ∀ (ε : ℤˣ) (ζ : ℂ), d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 →
    (ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) →
    ∃ ι : InfinitePlace F → (GR d.n →* d.G), (∀ w, Continuous (ι w)) ∧
      (∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ) ∧
      (∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1) ∧
      ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
theorem rdEx_of_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k) : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε, hs⟩ := h1 F E σ d
  rcases hs with ⟨hA, rfl⟩ | ⟨hA, rfl⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).1 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d (-1) 1 hε (Or.inl ⟨rfl, rfl⟩)
    exact ⟨⟨-1, 1, fr, sg, ι, hε, Or.inl ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
  · obtain ⟨fr, sg, hfr⟩ := (h2 F E σ d).2 hA
    obtain ⟨ι, hc, ha, ho, hf⟩ := h3 F E σ d 1 Complex.I hε (Or.inr ⟨rfl, rfl⟩)
    exact ⟨⟨1, Complex.I, fr, sg, ι, hε, Or.inr ⟨rfl, rfl⟩, hfr, hc, ha, ho, hf⟩⟩
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section GRpt
variable {n : ℕ}
end GRpt
theorem twoSidedW_k (hDW : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    (f : d.G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (h0 : ∀ z, ∫ x, f (R.ι w (nr x) * z) * ψ₀ x = 0) :
    ∀ (z : d.G) (a b : GR d.n), ∫ x, f (R.ι w (a * nr x * b) * z) * ψ₀ x = 0 := by
  intro z a b
  let Fz : d.G → M2 d.n → ℂ := fun h M => f (R.ι w (toGR' M) * h)
  let Γ : Set (M2 d.n) := {M | ∃ y' : GR d.n, M = mR y' ∧ ∃ γ ∈ rat2 σ d.Y, ∃ x : d.G, γ = x * R.ι w y' ∧
    ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x}
  have hcont : ∀ h, ContinuousOn (Fz h) {g | InG g} := by
    intro h
    rw [continuousOn_iff_continuous_domRestrict]
    have e : Set.domRestrict {g | InG g} (Fz h) = fun p : {M : M2 d.n | InG M} => f (R.ι w (mkG p.1 p.2) * h) := by
      funext p
      show f (R.ι w (toGR' p.1) * h) = _
      rw [toGR'_of p.2]
    rw [e]
    exact hf.comp (((R.cont w).comp continuous_mkG).mul continuous_const)
  have hΓG : ∀ γ ∈ Γ, InG γ := by
    rintro _ ⟨y', rfl, -⟩
    exact y'.2
  have hdense : {g | InG g} ⊆ closure Γ := by
    intro M hM
    rw [mem_closure_iff]
    intro U hU hMU
    obtain ⟨γ, hγ, y', hy'O, x, hγx, hx⟩ := hDW F E σ d R w (mkG M hM) (mR ⁻¹' U) (hU.preimage continuous_mR) hMU
    exact ⟨mR y', hy'O, y', rfl, γ, hγ, x, hγx, hx⟩
  have hperm : ∀ γ ∈ Γ, ∀ h, ∃ h', ∀ g, InG g → Fz h (γ * g) = Fz h' g := by
    rintro _ ⟨y', rfl, γ, hγ, x, hγx, hx⟩ h
    refine ⟨x⁻¹ * h, fun g hg => ?_⟩
    have e1 : mR y' * g = mR (y' * mkG g hg) := rfl
    have hy : R.ι w y' = γ * x⁻¹ := by rw [hγx, hx y', mul_inv_cancel_right]
    have hc : x⁻¹ * R.ι w (mkG g hg) = R.ι w (mkG g hg) * x⁻¹ := by
      have hc' : Commute x (R.ι w (mkG g hg)) := hx _
      exact hc'.inv_left.eq
    simp only [Fz]
    rw [e1, toGR'_mR, toGR'_of hg, map_mul, hy, mul_assoc, mul_assoc, hinv γ hγ, ← mul_assoc, hc, mul_assoc]
  have hvan : ∀ h g, InG g → ∫ x, Fz h (nU (herm x) * g) * ψ₀ x = 0 := by
    intro h g hg
    have e : ∀ x, Fz h (nU (herm x) * g) = f (R.ι w (nr x) * (R.ι w (mkG g hg) * h)) := fun x => by
      have e1 : nU (herm x) * g = mR (nr x * mkG g hg) := by rw [mR_mul', hnr, mR_mkG]
      simp only [Fz]
      rw [e1, toGR'_mR, map_mul, mul_assoc]
    simp_rw [e]
    exact h0 _
  have key := LVs.twoSided d.n d.G Fz Γ hcont hΓG hdense hperm ψ₀ hψc hψs hvan z (mR a) (mR b) a.2 b.2
  have e : ∀ x, Fz z (mR a * nU (herm x) * mR b) = f (R.ι w (a * nr x * b) * z) := fun x => by
    have e1 : mR a * nU (herm x) * mR b = mR (a * nr x * b) := by rw [mR_mul', mR_mul', hnr]
    simp only [Fz]
    rw [e1, toGR'_mR]
  simp_rw [e] at key
  exact key
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem a_pos_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : 0 < d.a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  rw [d.ok.hgt.val p t hp k hk]
  exact absE_pos _
theorem ht_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : ((d.Ht x : ℝ) : ℂ) = (d.a x : ℂ) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
  rw [Real.coe_toNNReal _ (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d x).le]
theorem isCompact_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCompact (d.K : Set d.G) :=
  _root_.PositivityTheory.SiegelWeilFormula.kunf.SecA.isCompact_stdK'_k d.B d.Y d.ok.good d.b d.K d.ok.stdK
theorem isClosed_siegelParabolic (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have e : (par2 σ d.Y : Set d.G) = (fun p : d.G => (inFrame d.b p).toBlocks₂₁) ⁻¹' {0} := by
    ext p
    exact mem_stabiliser_iff_lower_block_zero d.ok.frame p
  rw [e]
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  exact isClosed_singleton.preimage
    (continuous_pi fun i => continuous_pi fun j => hfr.matrix_elem (Sum.inr i) (Sum.inl j))
theorem continuous_a_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (_root_.PositivityTheory.SiegelWeilFormula.kunf.isClosed_siegelParabolic d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.isCompact_K_k d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, SecA.uDet_eq ht]
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsLevi_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : Prop :=
  ∃ t u : GL (Fin d.n) (AE F E), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
def IsPureT_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) : Prop :=
  ∃ (P : InfinitePlace F → PX d.m d.n)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ),
    (∀ v, IsLocallyConstant (g v) ∧ HasCompactSupport (g v)) ∧
    (∀ᶠ v in cofinite, g v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) *
      ∏ᶠ v, g v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def PureSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock →
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i) ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R (Φs i)) ∧ Φ = ∑ i, c i • Φs i
def CellFormula_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, ∀ (g x : d.G) (β : Mx F E d.n d.n),
    inFrame d.b g = Matrix.fromBlocks 1 β 0 1 →
      d.sec0 Φ (w * g * x) = ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram Z Z))) * d.T (d.om x Φ) Z ∂ν
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def Jd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ
structure Rel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : nF σ d.Y d.b) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1
def RelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ x t u, inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 → ∀ T : nF σ d.Y d.b, IsND T →
  ∃ (η : E) (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)),
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g ∧ (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ∧ (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧
    (Td η T₀).det ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν
def HeightDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹
def MeasDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ν,
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν → MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc
def ThetaDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH 𝓕 ∧
    ∀ (T : nF σ d.Y d.b) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (fun Y => d.T Φ (toMx Y))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀})
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section SDl
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def linRhoL_k (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem lin_T_sum_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : Mx F E d.m d.n) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by
  set_option synthInstance.maxHeartbeats 100000 in
    change d.l (linRhoL_k d X (∑ i ∈ s, c i • Φs i)) = ∑ i ∈ s, c i * d.l (linRhoL_k d X (Φs i))
    simp only [map_sum, map_smul, smul_eq_mul]
theorem constantTerm_finsetSum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (x : d.G) :
    d.sec0 (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.sec0 (Φs i) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_sum, map_smul, smul_eq_mul]
theorem lin_om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ h
theorem lin_S_mem_k (g : UA σ d.A.J) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch := d.ok.dbl.lin.pres g Φ h
theorem lin_sum_mem_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    ∑ i ∈ s, c i • Φs i ∈ d.sch :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (h i hi)
theorem lin_thetaSum_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    thetaSum F (∑ i ∈ s, c i • Φs i) = ∑ i ∈ s, c i * thetaSum F (Φs i) := by
  have h1 := (hT F E σ d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d s c Φs h)).1
  have h2 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => ∑ i ∈ s, c i * d.T (Φs i) (incM F X))
      (∑ i ∈ s, c i * thetaSum F (Φs i)) :=
    hasSum_sum fun i hi => ((hT F E σ d _ (h i hi)).1).mul_left (c i)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_T_sum_k] at h1
  exact h1.unique h2
theorem lin_I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn)
    (h : ∀ i ∈ s, Φs i ∈ d.sch) (x : d.G) : d.I (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.I (Φs i) x := by
  have e : ∀ g : UA σ d.A.J, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) =
      ∑ i ∈ s, c i * thetaSum F (d.om x (d.S g (Φs i))) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smul]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_thetaSum_sum_k d hT s c (fun i => d.om x (d.S g (Φs i))) fun i hi => _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_S_mem_k d g (h i hi))
  have hint : ∀ i ∈ s, IntegrableOn (fun g => thetaSum F (d.om x (d.S g (Φs i)))) d.D d.μ :=
    fun i hi => ((hA F E σ d).2.2 _ (h i hi)).1 x
  show ⨍ g in d.D, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) ∂d.μ =
    ∑ i ∈ s, c i * ⨍ g in d.D, thetaSum F (d.om x (d.S g (Φs i))) ∂d.μ
  simp only [e, setAverage_eq]
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (c i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_smul_comm]
end SDl
theorem lin_psi_meas_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : Mx F E d.n d.n) :
    Measurable (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) := by
  have key : ∀ β : nA σ d.Y d.b, d.B.ψ (-d.tt (M * β.1)) =
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) := by
    intro β
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib, lin_addChar_sum]
  rw [show (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext key]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  have hc : Continuous fun y : AE F E => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * y))) :=
    d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg
  exact hc.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtype_coe))
theorem lin_fc_sum_k (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    (T : nF σ d.Y d.b) (hND : IsND T) (x : d.G) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → d.G → ℂ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, ∀ γ ∈ rat2 σ d.Y, ∀ g, f i (γ * g) = f i g) :
    fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, c i • f i) T x = ∑ i ∈ s, c i * fc d.B.ψ d.b nb lam 𝓖 (f i) T x := by
  classical
  obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
  have hfun : ∀ s : Finset ι, (∑ i ∈ s, c i • f i) = fun a => ∑ i ∈ s, c i * f i a := by
    intro s; funext a; simp [Finset.sum_apply]
  have hcs : ∀ s : Finset ι, Continuous (∑ i ∈ s, c i • f i) := by
    intro s; rw [hfun s]; exact continuous_finsetSum s fun i _ => continuous_const.mul (hc i)
  have his : ∀ s : Finset ι, ∀ γ ∈ rat2 σ d.Y, ∀ g, (∑ i ∈ s, c i • f i) (γ * g) = (∑ i ∈ s, c i • f i) g := by
    intro s γ hγ g; rw [hfun s]; exact Finset.sum_congr rfl fun i _ => by rw [hi i γ hγ g]
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    simp only [one_smul, add_zero, one_mul] at h0
    simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hlin (c j) (f j) _ (hc j) (hcs s) (hi j) (his s), ih]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

