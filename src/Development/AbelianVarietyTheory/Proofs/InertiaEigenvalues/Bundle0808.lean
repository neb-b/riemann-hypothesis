module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0733
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.ThetaPoisson GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.RSTheta

section Row

variable {R : Type} [CommRing R] {a : ℕ}

def rowMat (ℓ : Fin a) (y : Fin a → R) : Matrix (Fin a) (Fin a) R := (1 : Matrix (Fin a) (Fin a) R).updateRow ℓ y

theorem det_rowMat (ℓ : Fin a) (y : Fin a → R) : (rowMat ℓ y).det = y ℓ := by
  have h := det_updateRow_sum (1 : Matrix (Fin a) (Fin a) R) ℓ y
  have e : ∑ k, y k • (1 : Matrix (Fin a) (Fin a) R) k = y := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply]
  rw [e] at h
  simpa [rowMat] using h

theorem isUnit_rowMat_iff {ℓ : Fin a} {y : Fin a → R} : IsUnit (rowMat ℓ y) ↔ IsUnit (y ℓ) := by
  rw [isUnit_iff_isUnit_det, det_rowMat]


open Classical in
def rowGL (ℓ : Fin a) (y : Fin a → R) : GL (Fin a) R :=
  if h : IsUnit (y ℓ) then (isUnit_rowMat_iff.2 h).unit else 1

theorem val_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) : (rowGL ℓ y).val = rowMat ℓ y := by
  rw [rowGL, dite_eq_left h, IsUnit.unit_spec]

theorem single_vecMul_rowGL {ℓ : Fin a} {y : Fin a → R} (h : IsUnit (y ℓ)) :
    Pi.single ℓ 1 ᵥ* (rowGL ℓ y).val = y := by
  rw [val_rowGL h, single_one_vecMul]
  exact updateRow_self

theorem rowGL_single (ℓ : Fin a) : rowGL ℓ (Pi.single ℓ (1 : R)) = 1 := by
  refine Units.ext ((val_rowGL (by simp)).trans ?_)
  have : (Pi.single ℓ 1 : Fin a → R) = (1 : Matrix (Fin a) (Fin a) R) ℓ := by
    funext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [rowMat, this]
  exact updateRow_eq_self _ _

end Row

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
variable (E) in
def rowSet (ℓ : Fin a) : Set (Fin a → Cinf E) := {u | ∀ w, u ℓ w ≠ 0}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem isUnit_of_mem_rowSet {ℓ : Fin a} {u : Fin a → Cinf E} (h : u ∈ rowSet E ℓ) : IsUnit (u ℓ) :=
  Pi.isUnit_iff.2 fun w => (h w).isUnit

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_rowSet (ℓ : Fin a) : IsOpen (rowSet E ℓ) := by
  rw [rowSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuousOn_rowGL (ℓ : Fin a) : ContinuousOn (rowGL ℓ) (rowSet E ℓ) := by
  refine GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.continuousOn_iff.2 ?_
  have h : Continuous fun u : Fin a → Cinf E => rowMat ℓ u := continuous_const.matrix_updateRow ℓ continuous_id
  exact h.continuousOn.congr fun u hu => val_rowGL (isUnit_of_mem_rowSet hu)

def rsInf (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (g : GA E a) (u : Fin a → Cinf E) : ℂ :=
  φ (g * (infGL E a (rowGL ℓ u))⁻¹) * conj (φ' (g * (infGL E a (rowGL ℓ u))⁻¹)) * Φ u

def rsPsi (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  thetaFn (rsInf ℓ φ φ' Φ g) J η y

theorem rsPsi_ratGL_mul (ℓ : Fin a) {φ φ' : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (h' : ∀ γ g, φ' (ratGL E a γ * g) = φ' g) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (γ : GL (Fin a) E) (g : GA E a) (y : Fin a → Ad E) :
    rsPsi ℓ φ φ' Φ J η (ratGL E a γ * g) y = rsPsi ℓ φ φ' Φ J η g y := by
  simp only [rsPsi, thetaFn, rsInf, mul_assoc, h, h']

theorem continuousOn_inv_rowGL (ℓ : Fin a) :
    ContinuousOn (fun u => (infGL E a (rowGL ℓ u))⁻¹) (rowSet E ℓ) :=
  (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn (continuousOn_rowGL ℓ)).inv

theorem continuous_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ tsupport Φ
  · have h1 : ContinuousAt (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) p :=
      continuousAt_fst.mul (ContinuousAt.comp (f := Prod.snd)
        ((continuousOn_inv_rowGL ℓ).continuousAt ((isOpen_rowSet ℓ).mem_nhds (hs hp))) continuousAt_snd)
    exact ((h.continuousAt.comp h1).mul ((Complex.continuous_conj.comp h').continuousAt.comp h1)).mul
      (hΦ.comp continuous_snd).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuousAt_snd.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [rsInf, hq]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpen_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsOpen (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => (isOpen_idealFiniteAdeles J).preimage (continuous_apply i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isCompact_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsCompact (latt a J) :=
  isCompact_pi_infinite fun _ => isCompact_idealFiniteAdeles J

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : IsClosed (latt a J) := by
  rw [latt, Set.setOf_forall]
  exact isClosed_iInter fun i =>
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles J)).preimage (continuous_apply i)

theorem continuous_rsPsi {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Continuous φ)
    (h' : Continuous φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) : Continuous fun p : GA E a × (Fin a → Ad E) => rsPsi ℓ φ φ' Φ J η p.1 p.2 := by
  have h1 : Continuous fun p : GA E a × (Fin a → Ad E) => (p.1, fun i => pInf E (p.2 i)) :=
    continuous_fst.prodMk (continuous_pi fun i =>
      GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_snd))
  have h2 : Continuous fun p : GA E a × (Fin a → Ad E) => (fun i => pFin E (p.2 i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp
      ((continuous_apply i).comp continuous_snd)).sub continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    (IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const)
  exact ((continuous_rsInf h h' hΦ hs).comp h1).mul (h3.comp h2)

theorem continuous_of_mem_smoothSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous F := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hS := GlobalTheory.ShortVecDecay.smoothSpan_le_Sm π (Submodule.subset_span hF)
    obtain ⟨f, φ, hf, hφ, rfl⟩ := hF
    refine ContAut.continuous_of_isOpen_stab E a ⟨_, hS⟩ (isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
    have e : (fun x => φ.1 (x * finGL E a k)) = φ.1 := congrArg Subtype.val hk
    exact (GlobalTheory.JSW.smoothInf_rt_fin f φ.1 k g).symm.trans (by rw [e])
  | zero => exact continuous_const
  | add F G _ _ hF hG => exact hF.add hG
  | smul z F _ hF => exact hF.const_smul z

theorem continuous_of_mem_or {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.smoothSpan π) :
    Continuous φ.1 :=
  h.elim (fun h => ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ h).1.level) continuous_of_mem_smoothSpan

end GlobalTheory.RSTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

namespace GlobalTheory.PointsDetectAlg

theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (hI : IntAll Xo c)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {ι : Type} [Fintype ι] (g : ι → Rul Xo c) (hg : ∀ s, g s ∈ sec Xo c a n)
    (hli : LinearIndependent c.F g) (w : ι → ℂ_[p])
    (hw : ∀ z : PtC Xo c φ, ∑ s, w s * valC z.1 (g s) = 0) : w = 0 := by
  by_contra hw0
  let wP : ι → PAt φ := w
  have hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    obtain ⟨z, u, hu, hz⟩ := _root_.GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom)
      (fun a => by simp [toCp_algebraMap]) y a n
    have h1 := hw z
    simp only [hz _ (hg _)] at h1
    have h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      change u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))
      ring
    exact (mul_eq_zero.1 h2).resolve_left hu
  let K := algebraicClosure c.F (PAt φ)
  let V : Set (ι → K) := {v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L)
    (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}
  obtain ⟨d, hd0, hd⟩ := _root_.GlobalTheory.linRelation_descend K (PAt φ) ι V wP hw0 (by
    rintro v ⟨L, _, _, _, σ, y, hv⟩
    simpa only [IntermediateField.algebraMap_apply, hv] using hrel L σ y)

  have hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    have hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V :=
      ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩
    have := congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)
    simpa using this

  let K0 := IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))
  have hfin : FiniteDimensional c.F K0 := IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact (mem_algebraicClosure_iff.1 (d s).2).isIntegral)
  letI : Module.Free c.F K0 := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  let bs := Module.finBasis c.F K0
  let m := Module.finrank c.F K0
  let e : Fin m → PAt φ := fun t => (bs t : PAt φ)
  have he : LinearIndependent c.F e :=
    bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)
  have hea : ∀ t, IsAlgebraic c.F (e t) := fun t =>
    (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val
  have dmem : ∀ s, (d s : PAt φ) ∈ K0 := fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩
  let q : ι → Fin m → c.F := fun s t => bs.repr ⟨d s, dmem s⟩ t
  have hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t := by
    intro s
    have h := congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)
    simp only [IntermediateField.coe_sum, Algebra.smul_def] at h
    exact h.symm
  let hh : Fin m → Rul Xo c := fun t => ∑ s, q s t • g s
  have hhsec : ∀ t, hh t ∈ sec Xo c a n := fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)
  have hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m),
      evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y := by
    intro L _ _ y t
    have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
      (fun s => q s t • g s) Finset.univ
    simp only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this
    exact this
  have hzero : ∀ t, hh t = 0 := by
    intro t
    refine _root_.GlobalTheory.Reg.sec_eq_zero_of_finite_values E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_
    have := GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by
      rw [← hdrel L σ y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    exact congrFun this t
  have hq0 : ∀ s t, q s t = 0 := fun s t =>
    Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s
  apply hd0
  funext s
  apply Subtype.ext
  rw [hq s]
  simp [hq0]

end GlobalTheory.PointsDetectAlg

namespace GlobalTheory.PointsDetectAlg

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

theorem detects : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), Detects YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx
  let bV := Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))
  let B := Algebra.TensorProduct.basis (NX.KB S i b) bV
  let r := B.repr x
  let g : r.support → T0.R ((j : ℕ) + 1) := fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))
  have hx' : x = ∑ s : r.support, r s • B s := by
    conv_lhs => rw [← B.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_coe_sort r.support (fun s => r s • B s)).symm
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0 := by
    intro z
    have h := hx z
    rw [hx'] at h
    have e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s) :=
      map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ
    rw [← h]
    refine Eq.trans ?_ e.symm
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm
    congr 1
    have hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _) :=
      Algebra.TensorProduct.basis_apply _ _
    refine Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm
    refine Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm
    exact (one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)
  have hli : LinearIndependent T0.Q.c.F g := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf s
    have h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hcf, map_sum]
      simp only [cuspOf_smul, RingEquiv.apply_symm_apply]
      push_cast
      rfl
    have h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0 :=
      (cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)
    have h3 := Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s
    simpa using h3
  have hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩
  have hw := core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli
    (fun s => iC (r s)) hval
  have hr : ∀ s : r.support, r s = 0 := fun s => (map_eq_zero iC).1 (congrFun hw s)
  rw [hx']
  exact (Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl

end GlobalTheory.PointsDetectAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelic
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

open GlobalTheory.IdemSupport

theorem idempotentFlip_mul_conjFlip_eq_one {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0)
    (hxy : x * y = 1) : (e * x + c * y + (1 - e - c)) * (c * x + e * y + (1 - c - e)) = 1 := by
  linear_combination (x*y - x - y + 1) * he + (x*y - x - y + 1) * hc + (x^2 + y^2 - 2*x - 2*y + 2) * hec + (e + c) * hxy

theorem complementIdempotent_mul_idempotentFlip {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0) :
    (1 - (e + c)) * (e * x + c * y + (1 - e - c)) = 1 - (e + c) := by
  linear_combination (1 - x) * he + (1 - y) * hc + (2 - x - y) * hec

theorem orthogonal_mul_idempotentFlip_sub_one_eq_zero {R : Type} [CommRing R] {e x y c f : R} (h1 : f * e = 0) (h2 : f * c = 0) :
    f * (e * x + c * y + (1 - e - c) - 1) = 0 := by
  linear_combination (x - 1) * h1 + (y - 1) * h2

theorem natCast_mul_incA_inv {D : D7} {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hm), map_one]

theorem cA_incA_natCast_inv {D : D7} (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [cA_incA, star_inv₀, star_natCast]

theorem cA_flipElt {D : D7} (e : AE D) (m : ℕ) :
    cA D (flipElt e m) = cA D e * (m : AE D) + e * incA D ((m : D.host.E)⁻¹) + (1 - cA D e - e) := by
  unfold flipElt
  rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_sub, map_sub, map_one, map_natCast, cA_incA_natCast_inv, cA_cA]

theorem flipElt_mul_cA {D : D7} {e : AE D} (he : e * e = e) (hec : e * cA D e = 0) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * cA D (flipElt e m) = 1 := by
  rw [cA_flipElt]
  exact idempotentFlip_mul_conjFlip_eq_one he (by rw [← map_mul, he]) hec (natCast_mul_incA_inv hm)

theorem flipElt_sub_one_mul {D : D7} {e f : AE D} (m : ℕ) (h1 : f * e = 0) (h2 : f * cA D e = 0) :
    f * (flipElt e m - 1) = 0 := by
  unfold flipElt
  exact orthogonal_mul_idempotentFlip_sub_one_eq_zero h1 h2

def scalGL {R : Type} [CommRing R] (n : ℕ) (a b : R) (h : a * b = 1) : GL (Fin n) R :=
  ⟨a • (1 : Matrix (Fin n) (Fin n) R), b • (1 : Matrix (Fin n) (Fin n) R),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, mul_comm, h, one_smul]⟩

theorem cT_scalar {R : Type} [CommRing R] (σ : R →+* R) (n : ℕ) (a : R) :
    Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) = σ a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp only [if_true, mul_one]
  · simp only [if_neg (Ne.symm hij), if_neg hij, mul_zero, map_zero]

theorem scalGL_mem_UJ {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : R)
    (h : a * b = 1) (hb : σ a = b) : scalGL n a b h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) * J * (a • (1 : Matrix (Fin n) (Fin n) R)) = J
  rw [cT_scalar, hb, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

def scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) : GA D V :=
  ⟨scalGL V.rank a (cA D a) ha, scalGL_mem_UJ _ _ a (cA D a) ha rfl⟩

theorem mt_scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a ha) = a • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

theorem scalar_sub_one_entry {R : Type} [CommRing R] {n : ℕ} {f a : R} (h : f * (a - 1) = 0) (i j : Fin n) :
    f * (a • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, mul_one]; exact h
  · rw [if_neg hij, mul_zero, sub_zero, mul_zero]

theorem oneAt_scalU {D : D7} (V : HSp D) {a : AE D} (ha : a * cA D a = 1) (l : ℕ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → algebraMap (AF D.host.F) (AE D) ε * (a - 1) = 0) :
    OneAt V l (scalU V a ha) := by
  intro v ε hε hlv i j
  rw [mt_scalU]
  exact scalar_sub_one_entry (h v ε hε hlv) i j

theorem flip_central_exists : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V T m eT hT hm
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have he : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT hT subset_rfl
  have hec : eT * cA D eT = 0 := hT.2
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, he]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  have hinv := flipElt_mul_cA he hec hm
  refine ⟨scalU V _ hinv, ?_, ?_, mt_scalU V _ hinv⟩
  · have hinf : infPart D eT = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (delta_of_isIdemAt hΦ (hes PP hPP)).1
    refine mem_GfC_of_suppF V (f := eT + cA D eT) ?_ ((suppF_iff V _ _).2 ?_)
    · rw [map_add (f := _), hinf, (parts_cA eT).1, hinf, map_zero, add_zero]
    · rw [mt_scalU, smul_smul]
      unfold flipElt
      rw [complementIdempotent_mul_idempotentFlip he hcc hec]
  · intro l hl
    refine oneAt_scalU V hinv l fun v ε hε hlv => ?_
    have h0 : algebraMap (AF D.host.F) (AE D) ε * eT = 0 := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      have hd := delta_of_isIdemAt hΦ (hes PP hPP)
      refine hΦ.ext' (by rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = PP
      · subst hQ
        by_cases hQv : Q.under (𝓞 D.host.F) = v
        · exfalso
          apply hl Q hPP
          have h1 := hlv
          rw [← hQv] at h1
          change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal at h1
          rwa [map_natCast] at h1
        · rw [(place_comp hΦ hε).2.2 Q hQv, zero_mul]
      · rw [hd.2.2 Q hQ, mul_zero]
    have h0' : algebraMap (AF D.host.F) (AE D) ε * cA D eT = 0 := by
      rw [← cA_algebraMap ε, ← map_mul, h0, map_zero]
    exact flipElt_sub_one_mul m h0 h0'

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
section
namespace GlobalTheory

theorem genericUnlinkedGL_outright : GlobalTheory.Published.GenericUnlinkedGL :=
  GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds

end GlobalTheory
end

