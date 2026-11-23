module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.FourierZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilHeightdictStd
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.Ht
namespace PositivityTheory.SiegelWeilFormula.HeightDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fin_std_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (t u : GL (Fin n) (AE F E)) (η : E) (hη : η ≠ 0) :
    (∀ v : HeightOneSpectrum (𝓞 F),
      Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) ∧
      Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) :
        Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
      ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
          PositivityTheory.PfSWUS.Loc.latO d.bs v) := by
  classical
  have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((t⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
      ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v) = 1 := by
      have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
      simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
    have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hη, map_one]
    have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
        (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
    latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
  have ent : ∀ M : Matrix (Fin n) (Fin n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
  filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin n) (AE F E)).1,
    ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs n] with v ht ht' hu hu' he he' hl
  refine ⟨?_, ?_⟩
  · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
  · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
      (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]
end PositivityTheory.SiegelWeilFormula.HeightDict
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem inFrame_mul_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b x y
theorem inFrame_one_k : inFrame d.b (1 : d.G) = 1 :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_one d.b
theorem inFrame_inj_k {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y :=
  PositivityTheory.SiegelWeilFormula.kunf.inFrame_injective d.b h
theorem isUnit_det_inFrame_k (x : d.G) : IsUnit (inFrame d.b x).det :=
  Matrix.isUnit_det_of_left_inverse (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x)
variable {d} {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
include hε
theorem inU_inFrame_k (x : d.G) : (inFrame d.b x)ᵀ * jF d.n ε * (inFrame d.b x).map (cA σ) = jF d.n ε :=
  PositivityTheory.SiegelWeilFormula.kunf.frame_eq hε x
theorem exists_of_inU_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Mᵀ * jF d.n ε * M.map (cA σ) = jF d.n ε) : ∃ x : d.G, inFrame d.b x = M := by
  set J : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := jF d.n ε with hJ
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hJJ : J * (((ε : ℤ) : AE F E) • J) = 1 := by
    rw [Matrix.mul_smul, hJ, jF, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    congr 1 <;> simp [smul_smul, hεε]
  have hT : Mᵀ * (J * M.map (cA σ) * (((ε : ℤ) : AE F E) • J)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, hJJ]
  have hu : IsUnit Mᵀ.det := Matrix.isUnit_det_of_right_inverse hT
  rw [Matrix.det_transpose] at hu
  exact PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε M M⁻¹ (Matrix.mul_nonsing_inv M hu) hM
end
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilLocSt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix
variable {n : ℕ}
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem abs_tw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : |2 * Real.pi * ((R.sg w : ℤ) : ℝ)| = 2 * Real.pi := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h, abs_of_pos Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
def ThetaPt_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, ∀ (x : d.G) (h : UA σ d.A.J),
  thetaSum F (d.om x (d.S h Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F X)
def SplitDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ g : d.G,
  ∃ (y₀ : GR d.n) (Ψ' : Mx F E d.m d.n → ℂ),
    (∀ Φ ∈ d.sch, ∀ f, IsSw f → d.T Φ = R.tens w f Ψ → ∀ y, d.T (d.om (g * R.ι w y) Φ) = R.tens w (L (y₀ * y) f) Ψ') ∧
    ∀ δ : ℝ, 0 < δ → R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' ∈ d.schM
def DecompW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (g : d.G),
  ∃ (x : d.G) (y₀ : GR d.n), g = x * R.ι w y₀ ∧ d.cw w (inFrame d.b x) = 1
def ThetaBdd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Fn ∈ d.schM, ∃ K : ℝ, ∀ h : UA σ d.A.J,
  Summable (fun X : Matrix (Fin d.m) (Fin d.n) E => ‖Fn (mat h⁻¹ * incM F X)‖) ∧
    ∑' X : Matrix (Fin d.m) (Fin d.n) E, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ K
def LocFamG_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L →
  ∀ (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) →
    ∃ Gf : GR d.n → ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ, (∀ (y : GR d.n) (t : ℝ), Gf y t = L (y * a t) (fP 1)) ∧
    (∀ y u, DifferentiableOn ℂ (fun z => Gf y z u) (strip X)) ∧
    (∀ u, ContinuousOn (fun q : GR d.n × ℂ => Gf q.1 q.2 u) (Set.univ ×ˢ strip X)) ∧
    (∀ q ∈ (Set.univ : Set (GR d.n)) ×ˢ strip X, ∃ N ∈ 𝓝 q, ∃ C δ : ℝ, 0 < δ ∧ ∀ q' ∈ N, q'.2 ∈ strip X → ∀ u,
      ‖Gf q'.1 q'.2 u‖ ≤ C * Real.exp (-δ * sq u)) ∧
    ∀ y : GR d.n, ((mR y).toBlocks₂₂).det ≠ 0 → ∀ (r : ℕ) u,
      iteratedDeriv r (fun z => Gf y z u) 0 = L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_cmb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  have e : d.cmb c i j = ∑ k, c (i, j, k) • (Algebra.TensorProduct.basis (AF F) d.bs) k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  show (Algebra.TensorProduct.basis (AF F) d.bs).repr (d.cmb c i j) l = c (i, j, l)
  rw [e, Module.Basis.repr_sum_self]
theorem detIm_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) :
    ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
      ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  haveI : IsTotallyComplex E := hcm.2.1
  set τ : E →+* ℂ := (d.B.emb w).1 with hτ
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
    intro f
    have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
    have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    have e4 := RingHom.congr_fun e3 f
    rw [ComplexEmbedding.conjugate_coe_eq] at e4
    rw [e1]
    exact Complex.conj_eq_iff_im.mp e4
  have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
      τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
    intro e
    conv_lhs => rw [← d.bs.sum_repr e]
    simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
  obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    rw [InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (hne x)
  intro hD
  apply he
  have h1 := hexp 1
  have h2 := hexp e
  set p := τ (algebraMap F E (d.bs.repr 1 0)) with hp
  set q := τ (algebraMap F E (d.bs.repr 1 1)) with hq
  set p' := τ (algebraMap F E (d.bs.repr e 0)) with hp'
  set q' := τ (algebraMap F E (d.bs.repr e 1)) with hq'
  have ip : p.im = 0 := hreal _
  have iq : q.im = 0 := hreal _
  have ip' : p'.im = 0 := hreal _
  have iq' : q'.im = 0 := hreal _
  rw [map_one] at h1
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2im := congrArg Complex.im h2
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
    ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
  linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
    (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
def realLinearCoordinates (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) :
    (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
    ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
  map_add' r s := by
    funext w a j
    simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
  map_smul' c r := by
    funext w a j
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
    conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
theorem realLinearCoordinates_injective (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr0
  have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
    intro w
    let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
    have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
      ext a j
      have h := congrFun (congrFun (congrFun hr0 w) a) j
      have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
      rw [star_eq_zero] at h'
      rw [Matrix.mul_apply]
      exact h'
    have h2 : Z = 0 := by
      have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [e, h1, Matrix.mul_zero]
    intro i j
    exact congrFun (congrFun h2 i) j
  funext k
  obtain ⟨i, j, l⟩ := k
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have h := hz v.1 i j
    rw [Fin.sum_univ_two] at h
    have hi := real_indep (_root_.PositivityTheory.SiegelWeilFormula.KFock.detIm_ne_k d v.1) h
    have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
    rw [ev] at hi
    fin_cases l
    · exact hi.1
    · exact hi.2
  · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))
theorem archEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
      ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
        L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
    simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
    ring
  have hinj := _root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates_injective d R hr
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨(LinearEquiv.ofBijective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
  funext a j
  show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
      ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
    star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
  rw [Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  rfl
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Cmb
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cmb_add_k (c c' : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (c + c') = d.cmb c + d.cmb c' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Pi.add_apply, Matrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
theorem cmb_eq_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) (i : Fin d.m) (j : Fin d.n) :
    d.cmb c i j = ∑ k, c (i, j, k) • Algebra.TensorProduct.basis (AF F) d.bs k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem crd_cmb'_k (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
theorem continuous_cmb_k : Continuous d.cmb := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_eq_k]
  exact continuous_finsetSum _ fun k _ => ((continuous_apply (i, j, k)).smul continuous_const)
theorem continuous_crd_k : Continuous d.crd := by
  obtain ⟨i1, -, -, -⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  refine continuous_pi fun k => ?_
  have hl : Continuous (((Finsupp.lapply k.2.2).comp (Algebra.TensorProduct.basis (AF F) d.bs).repr.toLinearMap :
      AE F E →ₗ[AF F] AF F)) := IsModuleTopology.continuous_of_linearMap _
  exact hl.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
def cmbE_k : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ₜ+ Mx F E d.m d.n where
  toFun := d.cmb
  invFun := d.crd
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k d
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k d
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_add_k d
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_cmb_k d
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KFock.continuous_crd_k d
end Cmb
theorem int_schM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : Integrable f ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KFock.cmbE_k d).symm
  have h1 : Integrable (f ∘ e) (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    refine intSchA _ ?_ _ inferInstance hf'
    exact congrArg (fun m => @MeasurableSpace.pi (Fin d.m × Fin d.n × Fin 2) (fun _ => AF F) fun _ => m) measAF_eq
  have h2 := (integrable_map_equiv e f).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem fourierZero_k : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k := by
  intro F E _ _ _ _ _ σ d nb lam 𝓖 hc f hf hper hfc
  funext g
  exact _root_.PositivityTheory.FTA.ZFC.fc_inj_pt_per_k d.ok.good d.b nb lam 𝓖 d.ok.frame hc f hf hper g fun T => hfc T g
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem sigma_sigma_of_good_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (a : E) : σ (σ a) = a := by
  obtain ⟨-, -, -, h⟩ := hB.cm
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [h, h, star_star]
theorem coefData_exists_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ nb lam 𝓖, CoefData (σ := σ) (Y := Y) b nb lam 𝓖 := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  obtain ⟨K, hK, hc⟩ := nF_cocompact hσ hb
  obtain ⟨lam, 𝓖, hlam, h𝓖, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (nA σ Y b) (nF σ Y b) K hK hc).1
  exact ⟨nbE σ Y b, lam, 𝓖, isNMap_nbE hσ hb, hlam, h𝓖, h1⟩
theorem coefEx_k : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k := fun _F _E _ _ _ _ _ _σ d => _root_.PositivityTheory.SiegelWeilFormula.kfour.coefData_exists_k d.ok.good d.ok.frame
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

