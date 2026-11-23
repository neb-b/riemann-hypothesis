module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

section Pull

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D D' : ℕ} {f : Y' ⟶ Y}
  {m : CxPts p' σ' → CxPts p σ}

namespace CxPts

theorem continuous_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) : Continuous m :=
  continuous_induced_rng.2
    (((Points.continuous_comp f).comp continuous_subtype_val).congr fun z => (hm z).symm)

theorem mem_ptsIn_preimage (hm : ∀ z, (m z).1 = z.1 ≫ f) {U : Y.Opens} {z : CxPts p' σ'} :
    z ∈ ptsIn p' σ' (f ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := by
  change _ ↔ ⊤ ≤ (m z).1 ⁻¹ᵁ U
  rw [hm]
  rfl

theorem ev_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (U : Y.Opens) (g : Γ(Y, U)) (z : CxPts p' σ') :
    ev p σ U g (m z) = ev p' σ' (f ⁻¹ᵁ U) (f.app U g) z := by
  rw [ev, ev, hm]
  exact valR_comp _ _ _ _

end CxPts

theorem AlgChart.holo_map (hm : ∀ z, (m z).1 = z.1 ≫ f) (c' : AlgChart p' σ' D')
    (c : AlgChart p σ D) : DifferentiableOn ℂ (c.e ∘ m ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (f.app _ (c.x a))).mono fun x (hv : x ∈ c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) =>
    ⟨hv.1, (mem_ptsIn_preimage hm).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_of_comp hm _ _ _)

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)}

theorem exists_eventuallyEq_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (c : AlgChart p' σ' D') {v : V D'}
    (hv : v ∈ c.e.target) {E : Type*} (g : CxPts p σ → E) :
    ∃ i, m (c.e.symm v) ∈ (R.chart i).e.source ∧
      (g ∘ m) ∘ c.e.symm =ᶠ[𝓝 v] (g ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ m ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (m (c.e.symm v))
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e ((R.chart i).e.open_source.preimage
    (continuous_of_comp hm))).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg g ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.comp_map {g : CxPts p σ → ℂ} (h : R.HoloOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.HoloOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (((R'.chart j).holo_map hm (R.chart i)).differentiableAt
      (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.comp_map {g : CxPts p σ → ℝ} (h : R.SmoothOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.SmoothOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ m ∘ (R'.chart j).e.symm) _ :=
    (contDiffOn_piLp 2).2 fun a => contDiffOn_real ho
      (differentiableOn_euclidean.1 ((R'.chart j).holo_map hm (R.chart i)) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

end AnRead

namespace Weight

variable {R : AnRead p σ D} {B : LB Y} {φ : Weight p σ B}

theorem IsSmooth.linComb (h : φ.IsSmooth R) {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts p' σ' → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a) (R' : AnRead p' σ' D') :
    (φ.linComb f ε m hm).IsSmooth R' := fun j c =>
  ContDiffOn.sum (f := fun a v => (ε a : ℝ) * φ.φ (j a) (m a ((R'.chart c).e.symm v))) fun a _ =>
    contDiffOn_const.mul ((((h (j a)).comp_map (isOpen_ptsIn _) (hm a) R').mono
      fun z hz => mem_of_mem_linComb (hm · z) hz a) c)

theorem IsSmooth.pull (h : φ.IsSmooth R) {q : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = q)
    (R' : AnRead q σ D') : (φ.pull f hf).IsSmooth R' :=
  h.linComb _ _ _ _ R'

end Weight

end Pull

section Conj

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {A B : LB Y}

theorem CxPts.ev_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) (g : Γ(Y, U)) :
    ev p σ' U g y' = starRingEnd ℂ (ev p σ U g y) := by
  rw [ev, h]
  exact valR_conjHomeomorph y.1 U hy g

theorem sum_normSq_vecMul_unitary {α : Type*} [Fintype α] [DecidableEq α] {U : Matrix α α ℂ}
    (hU : U ∈ Matrix.unitaryGroup α ℂ) (w : α → ℂ) :
    ∑ a, ‖Matrix.vecMul w U a‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key (x : α → ℂ) : ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj', Complex.ofReal_sum,
      Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.vecMul_one]

namespace Weight

theorem isConj_fsBasis_of_unitary {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' U : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (e : M' = M.map (starRingEnd ℂ) * U) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') := fun i y y' h hy => by
  rw [fsBasis_φ, fsBasis_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((b j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((b j).f i)) :=
    CxPts.ev_conj h hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, M j a * valR y.1 (B.U i) ((b j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

variable {φ : Weight p σ B} {φ' : Weight p σ' B}

end Weight

end Conj

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulInt
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isIntegral_smul_of_charpoly_coeff_mul_int
    (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ)
    (h : ∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) :
    IsIntegral ℤ ((M : ℤ) • x) := by
  set χ := (LinearMap.mulLeft ℚ x).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _

  have hx : Polynomial.aeval x χ = 0 := by
    have h1 : Polynomial.aeval (LinearMap.mulLeft ℚ x) χ = 0 := LinearMap.aeval_self_charpoly _
    have h2 : Polynomial.aeval (Algebra.lmul ℚ A x) χ = Algebra.lmul ℚ A (Polynomial.aeval x χ) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h3 : Algebra.lmul ℚ A x = LinearMap.mulLeft ℚ x := rfl
    rw [h3, h1] at h2
    have := congrArg (fun f : A →ₗ[ℚ] A => f 1) h2
    simpa using this.symm
  have hs : Polynomial.aeval (algebraMap ℚ A (M : ℚ) * x) (χ.scaleRoots (M : ℚ)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hx
  have hsmon : (χ.scaleRoots (M : ℚ)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one]
    exact hmon
  have hlift : χ.scaleRoots (M : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy n χ.natDegree with hn | hn | hn
    · obtain ⟨a, ha⟩ := h n
      refine ⟨a * (M : ℤ) ^ (χ.natDegree - n - 1), ?_⟩
      have he : χ.natDegree - n = (χ.natDegree - n - 1) + 1 := by omega
      rw [he, pow_succ, map_mul, map_pow, eq_intCast, eq_intCast, ← ha]
      push_cast
      ring
    · subst hn
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by simpa using hmon.coeff_natDegree.symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hsmon
  refine ⟨q, hqmon, ?_⟩
  have : Polynomial.aeval ((M : ℤ) • x) q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ, hq]
    convert hs using 2
    rw [Algebra.smul_def]
    simp
  simpa [Polynomial.aeval_def] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatrixIdentity_germ_pullback_chart : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.isMat_germ) | (exact GlobalTheory.HomFixMat.isMat_germ) | (intros; apply GlobalTheory.HomFixMat.isMat_germ  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaPRead

theorem isThetaP_restrict {G' H' S' Si Tau Y ι : Type} [MeasurableSpace H'] [AddCommGroup Si] [Module ℂ Si]
    [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup Y] [Module ℂ Y]
    {M : ι → Type} [∀ ρ, AddCommGroup (M ρ)] [∀ ρ, Module ℂ (M ρ)] (low : ∀ ρ, Submodule ℂ (M ρ))
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Si → S'}
    {io : (⨂[ℂ] ρ, low ρ) →ₗ[ℂ] Tau →ₗ[ℂ] Si} (L : Y →ₗ[ℂ] (H' → Tau)) (hL : Function.Injective L)
    (S : Submodule ℂ (H' → Tau)) (U : Y →ₗ[ℂ] ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)))
    (h : ∃ thP, Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L) thP ∧
      ∀ x (v : ∀ ρ, low ρ), U x (fun ρ => v ρ) = thP (L.rangeRestrict x) (PiTensorProduct.tprod ℂ v)) :
    Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L ⊓ S)
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) := by
  obtain ⟨thP, hP, hv⟩ := h
  have key : ∀ f : ↥(LinearMap.range L ⊓ S),
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : ((∀ ρ, M ρ) →ₘₗ[ℂ] (G' → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) f =
        thP (Submodule.inclusion inf_le_left f) := by
    intro f
    set x := (LinearEquiv.ofInjective L hL).symm (Submodule.inclusion inf_le_left f) with hx
    have h1 : L.rangeRestrict x = Submodule.inclusion inf_le_left f := by
      have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective L hL) (Submodule.inclusion inf_le_left f)
      rw [← hx] at this
      rw [← this]
      rfl
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod, Submodule.coe_subtype,
      PiTensorProduct.lift.tprod]
    rw [← hx, hv x v, h1]
  refine ⟨fun f e g => ?_, fun f e g => ?_⟩
  · exact hP.integ (Submodule.inclusion inf_le_left f) e g
  · rw [key f]
    exact hP.eq _ e g

theorem isThetaP_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.thP_thF → ∀ μ i, Lift.IsThetaP ((RecTie.toLiftReal R F tupT hm hTop hinj).measV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).fdV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ptW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ioK i) ((RecTie.toLiftReal R F tupT hm hTop hinj).Amt μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thC μ i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h μ i
  exact isThetaP_restrict _ _ _ _ _ (h i (tupT μ))

end GlobalTheory.ThetaPRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVector
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.WordWeight

theorem step {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℝ) (v : V)
    (hv : IsWeight E ν v) (a b : Fin n) :
    IsWeight E (ν + root a b) (E a b v) := by
  intro c
  have h := hE c c a b
  have h2 : E c c (E a b v) = E a b (E c c v) +
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) v := by
    rw [← h]; simp
  rw [h2, hv c, map_smul]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hbc : b = c
  · subst hca; subst hbc; simp
  · subst hca
    have : ¬ c = b := fun h => hbc h.symm
    simp [this, hbc]
    rw [add_smul, one_smul]
    rfl
  · subst hbc
    simp [hca]
    rw [add_smul, neg_smul, one_smul]
    rfl
  · have : ¬ c = b := fun h => hbc h.symm
    simp [hca, this, hbc]

theorem word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    ∀ (l : List (Fin n × Fin n)) (μ : Fin n → ℝ) (w : V), IsWeight E μ w →
    IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum)
      ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro l μ w hw
  induction l with
  | nil => simpa using hw
  | cons p l ih =>
    have := step E hE _ _ ih p.1 p.2
    simp only [List.map_cons, List.sum_cons, List.prod_cons, mul_apply_eq_comp]
    convert this using 1
    abel

end GlobalTheory.WordWeight

theorem GlobalTheory.wordWeight : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro n V _ _ E hE μ w hw l
  exact GlobalTheory.WordWeight.word E hE l μ w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquiv
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ Γ' G₁ G₂ _ _ _ _ e ι₁ ι₂ θ K₁ K₂ γ δ f φ
  have hprod : (ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom) = (ι₁.prod ι₂).comp e.toMonoidHom := by
    ext x <;> rfl
  have hR : ((ι₁.comp e.toMonoidHom).prod (ι₂.comp e.toMonoidHom)).range = (ι₁.prod ι₂).range := by
    rw [hprod, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map]
  have hS : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x) =
      Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
    intro x
    have h : stab (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) K₁ K₂ x =
        (stab ι₁ ι₂ K₁ K₂ x).comap e.toMonoidHom := by
      simp only [stab, Subgroup.comap_inf, Subgroup.comap_comap]
    rw [h]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv (fun a => by simp [Subgroup.mem_comap]))
  unfold pointSum
  simp only [hS]
  rw [hR]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalence
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lift_mem_levVP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P g0 κ hκ
  obtain ⟨hG, hpar, hr⟩ := hκ
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) = g0.1 := hr
  have hmem : finE (Vc D i) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (RecTie.datVP R i t P) := by
    refine ⟨hpar, ?_⟩
    rw [hrt]; exact g0.2
  refine ⟨⟨hG, hmem⟩, ?_⟩
  have e1 : Formalism.L2.DIV.ext1 (RecTie.datVP R i t P).P.H (RecTie.datVP R i t P).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ)) = (P.chi g0)⁻¹ := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ hmem.2]
    simp only [hrt]
    rfl
  have e2 : Formalism.L2.DIV.ext1 (flagL (R.datVt i t)).P.H (flagL (R.datVt i t)).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ)) = 1 := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ (show Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) ∈ (flagL (R.datVt i t)).P.H from Subgroup.mem_top _)]
    rfl
  have key : Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) =
      (P.chi g0)⁻¹ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) := by
    unfold Formalism.L2.DIV.levFn
    rw [e1, e2, one_mul, mul_assoc]
    rfl
  show ((Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) : ℂˣ) : ℂ) = _
  rw [key, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologyTwoSubsingleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ i : ℤ, Subsingleton (Ht q (sp B) 2 i) := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (exact GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_tateTwistCohomology_two_subsingleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupportStatement
section
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∀ y : G, F y ≠ 0 → massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  first | exact @GlobalTheory.massC_ne_zero_of_support | exact GlobalTheory.massC_ne_zero_of_support | (intros; apply GlobalTheory.massC_ne_zero_of_support <;> assumption)
end

