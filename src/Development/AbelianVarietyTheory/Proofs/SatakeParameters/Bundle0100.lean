module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

def infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def intA : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

variable {F}

def evF (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom

def ordAt (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  Subring.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

def sgT (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] Af F ⊗[F] E :=
  TensorProduct.map (GlobalTheory.AutFunCompare.sgV v) LinearMap.id

def IsIdemOf (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) : Prop :=
  infP F E e = 0 ∧ evF E v (finP F E e) = 1 ∧ ∀ w, w ≠ v → evF E w (finP F E e) = 0

variable {E}

omit [NumberField E] in
theorem evF_sgT_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) : evF E v (sgT E v y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_same]

omit [NumberField E] in
theorem evF_sgT_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v ⊗[F] E) : evF E w (sgT E v y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  | tmul a e =>
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleV F v a) ⊗ₜ e = _
    rw [GlobalTheory.AutFunCompare.evalV_singleV, Pi.single_eq_of_ne h, TensorProduct.zero_tmul]

omit [NumberField E] in
theorem evF_ext {z z' : Af F ⊗[F] E} (h : ∀ v, evF E v z = evF E v z') : z = z' :=
  GlobalTheory.LatticeLocalGlobal.ext_components z z' h

omit [NumberField E] in
theorem evF_finP_incl (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    evF E v (finP F E (inclR (AF F) x)) = inclR (Fv F v) x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F 1) ⊗ₜ x = (1 : Fv F v) ⊗ₜ x
  rw [map_one, map_one]


omit [NumberField E] in
theorem isIdemOf_algebraMap {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α = 0) :
    IsIdemOf E v (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α)) := by
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · show (0 : Ainf F) ⊗ₜ (1 : E) = 0
    exact TensorProduct.zero_tmul _ _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α ⊗ₜ (1 : E) = 1
    rw [h1]; rfl
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w α ⊗ₜ (1 : E) = 0
    rw [h2 w hw]; exact TensorProduct.zero_tmul _ _

variable [StarRing E] (hc : CMData F E) (V : HSpace E)

abbrev lamHat (F : Type) [Field F] [NumberField F] [Algebra F E] (V : HSpace E) :
    AddSubgroup (Fin V.rank → Af F ⊗[F] E) :=
  latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0}

def locMat (v : HeightOneSpectrum (𝓞 F)) : HA (AF F) hc.sig V.gram →* GL (Fin V.rank) (Fv F v ⊗[F] E) :=
  (Formalism.UG.bc (evF E v)).comp ((Formalism.UG.bc (finP F E)).comp (HR (AF F) hc.sig V.gram).subtype)

def Supp (f : AF F ⊗[F] E) (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ i j, f * ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j = ((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j

def IsFin (g : HA (AF F) hc.sig V.gram) : Prop :=
  Formalism.UG.bc (infP F E) (HA.mat (AF F) hc.sig V.gram g) = 1

def Stab (g : HA (AF F) hc.sig V.gram) : Prop :=
  ∀ y, y ∈ lamHat F V ↔ (finMat hc.sig V.gram g).mulVec y ∈ lamHat F V

def DivG (e : AF F ⊗[F] E) (ϖ : E) (d : Fin V.rank → ℤ) (α : HA (AF F) hc.sig V.gram) : Prop :=
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E),
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → (fun a => finP F E e * B.mulVec z a) ∈ lamHat F V) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * y a) = fun a => finP F E e * B.mulVec z a) ∧
    (∀ y ∈ lamHat F V, ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) ∧
    (∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ lamHat F V,
      (fun a => finP F E e * (finMat hc.sig V.gram α).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a)

theorem locMat_val (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    (locMat hc V v g).1 = (finMat hc.sig V.gram g).map (evF E v) := rfl

theorem locMat_mem (v : HeightOneSpectrum (𝓞 F)) (g : HA (AF F) hc.sig V.gram) :
    locMat hc V v g ∈ HR (Fv F v) hc.sig V.gram :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V v (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projFin hc V g)).2

theorem mem_lamHat_iff (y : Fin V.rank → Af F ⊗[F] E) :
    y ∈ lamHat F V ↔ ∀ v, (fun i => evF E v (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v :=
  GlobalTheory.LatticeLocalGlobal.mem_latHat_iff F E V y

def IsFrameAt (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) : Prop :=
  ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ ∀ i, (h⁻¹).1.mulVec x i ∈ ordAt E v

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

theorem mem_ordAt_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (z : LocAlg v) :
    z ∈ ordAt E v ↔ z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le (t := (locOrder v).toSubring)).2 ?_ hz
    rintro _ ⟨a, ha, x, rfl⟩
    have := mul_mem ((locOrder v).algebraMap_mem ⟨a, ha⟩) (locEmb_mem_locOrder v x)
    have e : algebraMap (v.adicCompletionIntegers (maximalRealSubfield E)) (LocAlg v) ⟨a, ha⟩ * locEmb v (x : E) =
        a ⊗ₜ (x : E) := by
      show (a ⊗ₜ 1 : LocAlg v) * (1 ⊗ₜ (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e] at this
    exact this
  · intro hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Subring.subset_closure ⟨1, one_mem _, a, rfl⟩
    | algebraMap r => exact Subring.subset_closure ⟨r, r.2, 1, rfl⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_orthonormal (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ h : GL (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), IsFrameAt V v h ∧
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 * JR (Fv (maximalRealSubfield E) v) V.gram * h.1 = 1 := by
  haveI := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (V.gramᵀ a b) = V.gramᵀ b a :=
    fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd
    (GlobalTheory.LocalConjugacy.isLattice_coordLat V V.L0 V.standardTuple_isLattice)
    (GlobalTheory.LocalConjugacy.selfDual_coordLat V V.L0 V.baseLattice_isUnimodular) v
  refine ⟨h, fun x => (GlobalTheory.LocalConjugacy.mem_latLoc_iff V v x).trans ((h2 x).trans
    (forall_congr' fun i => (mem_ordAt_iff v _).symm)), ?_⟩
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  exact h3

end CM

end GlobalTheory.PlaceComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.SplitOfNegPrime

theorem sqrt_neg_not_mem_maximalRealSubfield (L : Type) [Field L] [NumberField L] [IsCMField L]
    (p : ℕ) (δ : L) (hp : 0 < p) (hδ : δ ^ 2 = -(p : L)) : δ ∉ maximalRealSubfield L := by
  intro hmem
  let x : maximalRealSubfield L := ⟨δ, hmem⟩
  have hx : x ^ 2 = -(p : maximalRealSubfield L) := Subtype.ext (by simpa [x] using hδ)
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have hv : v.IsReal := IsTotallyReal.isReal v
  have h := congrArg (InfinitePlace.embedding_of_isReal hv) hx
  rw [map_pow, map_neg, map_natCast] at h
  have h1 : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv x)]

theorem isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L), 0 < p → δ ^ 2 = -(p : L) → ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 → ∀ w : HeightOneSpectrum (𝓞 L), (q : 𝓞 L) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro L _ _ _ p q δ hp hδ hdvd w hw
  set Lp := maximalRealSubfield L
  set u := w.under (𝓞 Lp)
  obtain ⟨k, hk⟩ := hdvd
  set z : 𝓞 Lp := -(2 * (q : 𝓞 Lp) * (k : 𝓞 Lp)) with hz
  have hq : (q : 𝓞 Lp) ∈ u.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  have hzu : z ∈ u.asIdeal := by
    rw [hz]
    exact u.asIdeal.neg_mem_iff.2 (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq))
  have hk' : ((p : ℤ) : 𝓞 Lp) + 1 = (((8 * q : ℕ) : ℤ) : 𝓞 Lp) * (k : 𝓞 Lp) := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 Lp) hk
  have hsq : (1 + 4 * z : 𝓞 Lp) = -(p : 𝓞 Lp) := by
    rw [hz]
    push_cast at hk'
    linear_combination hk'
  have h1 := GlobalTheory.HenselSquare.isSquare_one_add_four_mul Lp u z hzu
  rw [hsq] at h1
  refine GlobalTheory.SplitOfSquare.isSplitAt_of_isSquare L (-(p : Lp)) δ (by rw [hδ]; push_cast; rfl)
    (sqrt_neg_not_mem_maximalRealSubfield L p δ hp hδ) w ?_
  simpa using h1

end GlobalTheory.SplitOfNegPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerJ.FiCore

theorem isVal_sum {ι Yv : Type} [Fintype ι] {n : ℕ} (fr : Yv → ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → Yv → ℂ) (h : ∀ c, IsVal fr lam (RingHom.id ℂ) (f c)) :
    IsVal fr lam (RingHom.id ℂ) (∑ c ∈ s, w c • f c) := by
  choose P hP hf using h
  refine ⟨∑ c ∈ s, w c • P c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hP c), ?_⟩
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, evG, MvPolynomial.eval₂_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem lawAt_sum {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (i : ℕ)
    (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)
    {κ : Type} (s : Finset κ) (w : κ → ℂ) (f : κ → C.Y i → ℂ) (h : ∀ c, LawAt O i g (f c)) :
    LawAt O i g (∑ c ∈ s, w c • f c) := by
  intro y y' hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [h c y y' hy]; ring

theorem K_mem_Fi : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  intro D u C A Pm M O G hF hU hd hT i hi φ hφ
  have hv := hF.1 i hi.le φ hφ
  refine (hF.2 (i + 1) (Nat.le_add_left 1 i) hi _).2 fun c' => ?_
  have hK : C.K i φ c' = ∑ c, C.wt i c • C.Kmap i c c' (φ c) := by
    simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM]
  rw [hK]
  exact ⟨isVal_sum _ _ _ _ _ fun c => _root_.GlobalTheory.KerJ.Kmap_isVal D u C A Pm M O i hi (hU i hi) c c' _ (hv c),
    fun g hg => lawAt_sum O _ g _ _ _ fun c =>
      _root_.GlobalTheory.KerJ.lawAt_Kmap D u C A Pm M O i hi (hU i hi) c c' (hd i hi c c') g (hT i hi c c' g hg) _ (hv c)⟩

end GlobalTheory.KerJ.FiCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapApplyEqMulVec
section
namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLocSpOfNatCastSmulMem
section
noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCardMatricesMulEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_left_kernel_matrices_eq_pow : ∀ (k : Type) [Field k] [Finite k] (m n j : ℕ) (A : Matrix (Fin n) (Fin n) k), Module.finrank k (LinearMap.range A.mulVecLin) + j = n → Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  first | exact @GlobalTheory.natCard_matrices_mul_eq_zero | exact GlobalTheory.natCard_matrices_mul_eq_zero | (intros; apply GlobalTheory.natCard_matrices_mul_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.IntegralAtPlace

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := ℂ_[p])).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  intro D p hpF hpd φ a ha
  obtain ⟨-, -, hqd, -, hd2⟩ := hypOdd_of_hostHyp D.host.hyp
  have hint : ∀ y : 𝓞 D.host.E, ‖φ (y : D.host.E)‖ ≤ 1 := fun y => by
    have h : IsIntegral ℤ (φ (y : D.host.E)) := by
      obtain ⟨f, hf, hx⟩ := RingOfIntegers.isIntegral_coe y
      refine ⟨f, hf, ?_⟩
      have := congrArg φ hx
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [RingHom.ext_int (φ.comp (algebraMap ℤ D.host.E)) (algebraMap ℤ ℂ_[p])] at this
    exact norm_le_one_of_isIntegral h
  let Q : Ideal (𝓞 D.host.E) :=
    { carrier := {y | ‖φ (y : D.host.E)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        rw [norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint c)) hx }
  have hmem : ∀ y, y ∈ Q ↔ ‖φ (y : D.host.E)‖ < 1 := fun y => Iff.rfl
  haveI hQ : Q.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
    · have h1 := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at h1
    · rw [hmem, show ((x * y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) * y from rfl, map_mul,
        norm_mul] at hxy
      by_contra hc
      push_neg at hc
      rw [hmem, hmem, not_lt, not_lt] at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  have hpQ : (p : 𝓞 D.host.E) ∈ Q := by
    rw [hmem]
    have e : ((p : 𝓞 D.host.E) : D.host.E) = (p : D.host.E) := by simp
    rw [e, map_natCast]
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨z, hz, hden⟩ := GlobalTheory.AAUnitAway.exists_den D Q hpF.out (by rw [hpd]; exact UpperTheory.Small.d_not_mem D.host)
    (by rw [hpd]; exact hqd.symm) hpQ
  have hz1 : ‖φ (z : D.host.E)‖ = 1 := le_antisymm (hint z) (not_lt.1 ((hmem z).not.1 hz))
  obtain ⟨w, hw⟩ := hden a ha
  have := hint w
  rwa [hw, map_mul, norm_mul, hz1, mul_one] at this

end GlobalTheory.IntegralAtPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomainStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedShift_fixed_ratio_const_domain : ∀ {B G : Type} [CommRing B] [IsDomain B] [CharZero B] (σ : G → B ≃+* B) (τ : G → B),
  (∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g) →
  ∀ p q : Polynomial B, q ≠ 0 →
  (∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) = (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) →
  ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  first | exact @GlobalTheory.InvRatFun.fixed_ratio_const | exact GlobalTheory.InvRatFun.fixed_ratio_const | (intros; apply GlobalTheory.InvRatFun.fixed_ratio_const <;> assumption)
end

