module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SigDet

theorem det_ne_zero_of_hasSig : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → M.det ≠ 0 := by
  intro n M r s h
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hB
  have key : Bᵀ * M * B.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    have t1 : Bᵀ = Aᵀ.submatrix e.symm id := rfl
    have t2 : B.map star = (A.map star).submatrix id e.symm := rfl
    rw [t1, t2, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  rw [Matrix.det_neg] at hd
  simp at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

end GlobalTheory.SigDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
section
noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (σ) in
def finK {n : ℕ} (W : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ W.J) :=
  {x | ∃ k ∈ KInf σ W τ, ∃ g ∈ UAt σ W (fun u : AF F => u.2), x = k * g}

variable {a a' : ℕ}

structure InducedMaj (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop where
  cartan : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)
  tie : ∀ w, ∃ a : Fin n₁ → ℂ, Y.θ w * (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) =
    (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) * Y₁.θ w

theorem InducedMaj.of_comm {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w))
    (h₂ : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w) : InducedMaj B H Y Y₁ :=
  ⟨h₁, fun w => ⟨0, by
    have e : Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) (0 : Fin n₁ → ℂ) = 0 := by ext; simp [Matrix.vecMulVec_apply]
    rw [e, add_zero]; exact h₂ w⟩⟩


variable (σ) in
def IsIsoPlane (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) ∧ InducedMaj B H Y Y₁

theorem IsIsoPlane.of_adapted {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w))
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) : IsIsoPlane σ B H Y Y₁ :=
  ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, h, .of_comm h₁ fun w => (hH.cartan w).1⟩

end GlobalTheory.ThK.DescB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DimCover

theorem exists_trdeg_eq_and_dim_eq {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f]
    [Flat f] : ∃ d : ℕ, Algebra.trdeg ℤ (X.residueField (genericPoint X)) = d ∧
      topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have H := IsPullback.of_hasPullback f (spMap (algebraMap ℤ ℚ))
  have := IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f H
  have hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  rw [hr₁] at r₁
  refine ⟨d, ?_, IntModel.topologicalKrullDim_eq_succ Int.not_isField H
    ((topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁)⟩
  have hb : Function.Bijective (IsLocalRing.residue X.functionField) :=
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  have e := ((RingEquiv.ofBijective _ hb).toIntAlgEquiv).trdeg_eq
  exact e.symm.trans
    ((congrArg (@Algebra.trdeg ℤ X.functionField _ _) (Subsingleton.elim _ _)).trans hd)

theorem charZero_residueField {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [Flat f] :
    CharZero (X.residueField (genericPoint X)) := by
  have := (flat_int_iff_charZero f).1 inferInstance
  have : CharZero X.functionField :=
    ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.charZero_iff
      (germ_injective_of_isIntegral X _ _)).1 this
  exact ((IsLocalRing.residue X.functionField).charZero_iff (RingHom.injective _)).1 this

theorem topologicalKrullDim_eq (k : Type) [CommRing k] (Y Z : Scheme.{0}) [IsIntegral Y]
    [IsIntegral Z] (p : Y ⟶ Sp k) (q : Z ⟶ Sp k) (D : ℕ) (h : IsArithVar p D) (hq : IsProjOver q)
    (hf : Flat (q ≫ spMap (Int.castRingHom k))) (g : Z ⟶ Y) (_ : g ≫ p = q)
    (hη : g (genericPoint Z) = genericPoint Y) (hd : g.residueDegree (genericPoint Z) ≠ 0) :
    topologicalKrullDim Z = (D + 1 : ℕ) := by
  have := h.finite
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this
  have := CommonModel.isProper_of_isProjOver hq
  have := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.flat
  obtain ⟨a, ha, ha'⟩ := exists_trdeg_eq_and_dim_eq (p ≫ spMap (Int.castRingHom k))
  obtain ⟨b, hb, hb'⟩ := exists_trdeg_eq_and_dim_eq (q ≫ spMap (Int.castRingHom k))
  rw [← hη] at ha
  let := (g.residueFieldMap (genericPoint Z)).hom.toAlgebra
  have : Module.Finite (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have : CharZero (Y.residueField (g (genericPoint Z))) :=
    hη ▸ charZero_residueField (p ≫ spMap (Int.castRingHom k))
  have e := trdeg_eq_of_isAlgebraic_top ℤ (Y.residueField (g (genericPoint Z)))
    (Z.residueField (genericPoint Z))
  obtain rfl : b = a := by exact_mod_cast hb.symm.trans (e.trans ha)
  rw [hb', ← ha', h.dim_eq]

end GlobalTheory.DimCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem irrUnitary_trace_ne_zero_copyFinDS : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ c hc hc0
  have hcomp : HasDSComp M π := _root_.GlobalTheory.hasDSComp_of_trace_ne_zero hDS hFl hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := _root_.GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm D V S M H π hπ hcomp hU
  obtain ⟨hirr, hadm⟩ := _root_.GlobalTheory.FinPartIrrAdm.irreducible_admissible hFl D V S M H π hπ hcomp hU
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := _root_.GlobalTheory.FinTrace.hasTrace_finFn D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := _root_.GlobalTheory.AutMult.hasTrace_repOp_of_isCopyFinDS D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuNorm

open scoped Pointwise

def mulUnitCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a : Rˣ) : R ≃ₜ+ R where
  toFun x := (a : R) * x
  invFun x := ((a⁻¹ : Rˣ) : R) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem distribHaarChar_eq_addEquivAddHaarChar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R] (a : Rˣ) :
    distribHaarChar R a = addEquivAddHaarChar (mulUnitCE a) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hKn).ne'
  have hT : μ K ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hT ?_
  have e := addEquivAddHaarChar_smul_preimage μ (X := a • K) (mulUnitCE a)
  have hpre : (mulUnitCE a : R → R) ⁻¹' (a • K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := (Units.mul_right_inj a).1 hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre] at e
  rw [← e]
  rfl

def evalUnitCE (R : Type) [AddCommGroup R] [TopologicalSpace R] : (Unit → R) ≃ₜ+ R where
  toFun f := f ()
  invFun x := fun _ => x
  left_inv f := rfl
  right_inv x := rfl
  map_add' f g := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

theorem modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F →
    ∀ t : (AE F E)ˣ, (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) : ℝ≥0) : ℝ) = (absE F E t : ℝ) := by
  intro F E _ _ _ _ _ hF t
  haveI := hF
  letI : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  set a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) t with ha
  let M : Matrix Unit Unit (AF F) := fun _ _ => (a : AF F)
  have hdet : M.det = (a : AF F) := Matrix.det_unique M
  have hM : IsUnit M.det := hdet ▸ a.isUnit
  have hχ := GlobalTheory.ModuLR.chi_AF F M hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (evalUnitCE (AF F)) (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : ((evalUnitCE (AF F)).symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (evalUnitCE (AF F)) = mulUnitCE a := by
    ext x
    show (M *ᵥ fun _ => x) () = (a : AF F) * x
    simp [Matrix.mulVec, dotProduct, M]
  rw [hext] at htr
  show ((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) = _
  rw [show distribHaarChar (AdeleRing (𝓞 F) F) a = distribHaarChar (AF F) a from rfl,
    distribHaarChar_eq_addEquivAddHaarChar, htr, hχ, hdet]
  exact GlobalTheory.absE_eq_prod_norm_fstA_sndA F E t

end GlobalTheory.ModuNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledFockVacuumEqSmulVacuumMulConj
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section
namespace GlobalTheory.RealLift.VacBox

def eL {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))

def eR {R S : ℕ} : Ix R S → Ix (R + S) (S + R) :=
  Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))

theorem dbl_cols {α β : Type} [Fintype β] {P Q R S : ℕ} (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ) :
    (A * c * (dblM C)ᵀ).toCols₁ = A * c.submatrix id eL * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ = A * c.submatrix id eR * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eL = Jm P Q * c.submatrix id eL * Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id eR = -(Jm P Q * c.submatrix id eR * Jm R S) :=
  _root_.GlobalTheory.RealLift.Dbl.dblM_colBlocks α β P Q R S A C c

theorem heisOp_rot_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 :=
  _root_.GlobalTheory.HeisRot.heisOp_rot_one P Q R S c t

theorem box_deriv {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) :=
  GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj F κ a₁ b₁ a₂ b₂ f g₁ g₂ f₀ h hg₁ hg₂ hh hf₀ x

def conjS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem sumPl_smul_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (L L' : ι → Module.End ℂ V) (v : V) (z : ℂ) (h : ∀ w, L' w v = z • L w v) :
    sumPl (V := fun _ : ι => V) L' (PiTensorProduct.tprod ℂ fun _ => v) =
      z • sumPl (V := fun _ : ι => V) L (PiTensorProduct.tprod ℂ fun _ => v) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl, PiTensorProduct.map_tprod]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ∀ M : Module.End ℂ V, (fun i => Function.update (fun i => (LinearMap.id : V →ₗ[ℂ] V)) w M i v) =
      Function.update (fun _ => v) w (M v) := by
    intro M; funext i
    by_cases hi : i = w
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [e, e, h w]
  exact MultilinearMap.map_update_smul _ _ _ _ _

theorem sub_smul' {m n k : Type} (z : ℂ) (M : Matrix m n ℂ) (e : k → n) :
    (z • M).submatrix id e = z • M.submatrix id e := rfl

theorem toCols_at {F E α β₁ β₂ : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {u : Matrix α (β₁ ⊕ β₂) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evI F) u) : At (evI F) u.toCols₁ ∧ At (evI F) u.toCols₂ :=
  ⟨fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inl j),
   fun r hr => by ext i j; exact congrFun (congrFun (hu r hr) i) (Sum.inr j)⟩

theorem vac_box : DerEx → VacLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ))
    (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ)),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsDblCoord (cA σ) (-1) JA JB d dd →
    IsFockMap ψ τ dd A (fun w => dblM (C w)) Φd →
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr)) := by
  intro hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d dd a b A C Φ Φd hCM hψ hFr hΦ hdd hΦd
  obtain ⟨D, hD1⟩ := hD F E σ α β κ ψ JA JB d hψ
  obtain ⟨Dd, hDd⟩ := hD F E σ α (β ⊕ β) (κ ⊕ κ) ψ JA (dbl JB) dd hψ
  set f₁ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hf₁
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f₁ (conjS f₁)
  have hf₀' : ∀ x, f₀ x = f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) := fun x => hf₀ x
  have hFrd := GlobalTheory.T.doubled_hermitian_space_frame_of_frame F E α β P Q R S τ JA JB a b A C hFr
  have hder : ∀ u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u₁ → ∀ c₁ : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u₁.map (piInf (τ w)) = A w * c₁ w * (C w)ᵀ) →
      D u₁ f₁ = Φ (sumPl (fun w => heisOp (c₁ w)) (PiTensorProduct.tprod ℂ fun _ => 1)) := fun u₁ hu₁ c₁ hc₁ =>
    GlobalTheory.SDUnique.sd_unique ((hD1 u₁ hu₁ f₁).1) (hΦ.2 u₁ hu₁ c₁ hc₁ _)
  have hbox : ∀ u : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ x, Dd u f₀ x =
      D u.toCols₁ f₁ (x ∘ Sum.inl) * star (f₁ (x ∘ Sum.inr)) +
        f₁ (x ∘ Sum.inl) * star (D u.toCols₂ f₁ (x ∘ Sum.inr)) := by
    intro u hu x
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine box_deriv (d.e u.toCols₁).1 (d.e u.toCols₁).2 (d.e u.toCols₂).1 (d.e u.toCols₂).2 f₁ _ _ f₀ _
      ((hD1 _ hu₁ f₁).2) ((hD1 _ hu₂ f₁).2) (fun y => ?_) hf₀' x
    rw [(hDd u hu f₀).2 y, e]
  have key : ∀ u u' : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
      ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (dblM (C w))ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * (((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) •
        (Jm P Q * c w * Jm (R + S) (S + R))) * (dblM (C w))ᵀ) →
      ∀ f f' : SInf F (κ ⊕ κ), SD (fun t => dd.rho ψ (realAd F t • u)) f₀ f →
        SD (fun t => dd.rho ψ (realAd F t • u')) f₀ f' → f' = Complex.I • f := by
    intro u u' hu hu' c hc hc' f f' hf hf'
    rw [← GlobalTheory.SDUnique.sd_unique ((hDd u hu f₀).1) hf, ← GlobalTheory.SDUnique.sd_unique ((hDd u' hu' f₀).1) hf']
    obtain ⟨hu₁, hu₂⟩ := toCols_at hu
    obtain ⟨hu₁', hu₂'⟩ := toCols_at hu'
    have hI : ∀ w, ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) = ((1 : ℝ) : ℂ) * Complex.I := fun w => by simp
    have h1 := hder _ hu₁ (fun w => (c w).submatrix id eL) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).1, ← hc w]; rfl)
    have h2 := hder _ hu₂ (fun w => (c w).submatrix id eR) (fun w => by
      rw [← (dbl_cols (A w) (C w) (c w)).2.1, ← hc w]; rfl)
    have h1' := hder _ hu₁' (fun w => (((1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eL * Jm R S))
      (fun w => by
        rw [← (dbl_cols (A w) (C w) (c w)).2.2.1, ← sub_smul', ← hI w,
          ← (dbl_cols (A w) (C w) _).1, ← hc' w]; rfl)
    have h2' := hder _ hu₂' (fun w => (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S))
      (fun w => by
        have e : (((-1 : ℝ) : ℂ) * Complex.I) • (Jm P Q * (c w).submatrix id eR * Jm R S) =
            ((((1 : InfinitePlace F → ℤˣ) w : ℤ) : ℂ) * Complex.I) • (-(Jm P Q * (c w).submatrix id eR * Jm R S)) := by
          rw [hI w, smul_neg, ← neg_smul]; congr 1; push_cast; ring
        rw [e, ← (dbl_cols (A w) (C w) (c w)).2.2.2, ← sub_smul', ← (dbl_cols (A w) (C w) _).2.1, ← hc' w]; rfl)
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ 1)] at h1'
    rw [sumPl_smul_tprod _ _ _ _ (fun w => heisOp_rot_one _ (-1))] at h2'
    rw [map_smul] at h1' h2'
    ext x
    rw [SchwartzMap.smul_apply, hbox u' hu' x, hbox u hu x, h1', h2', h1, h2]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  obtain ⟨z', hz'⟩ := hV F E σ α (β ⊕ β) (κ ⊕ κ) P Q (R + S) (S + R) ψ τ JA (dbl JB) dd a b A
    (fun w => dblM (C w)) Φd hCM hψ hFrd hΦd f₀ 1 key
  have hne1 : f₁ ≠ 0 := fun h0 => _root_.GlobalTheory.tprod_one_pol_ne_zero F P Q R S (hΦ.1 (h0.trans (map_zero Φ).symm))
  obtain ⟨y, hy⟩ : ∃ y, f₁ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne1 (SchwartzMap.ext h)
  have hz0 : z' ≠ 0 := by
    rintro rfl
    have h := congrArg (fun g : SInf F (κ ⊕ κ) => g (Sum.elim y y)) hz'
    simp only [zero_smul, SchwartzMap.zero_apply, hf₀', Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    exact mul_ne_zero hy (star_ne_zero.2 hy) h
  refine ⟨z'⁻¹, inv_ne_zero hz0, fun x => ?_⟩
  have h := congrArg (fun g : SInf F (κ ⊕ κ) => g x) hz'
  simp only [SchwartzMap.smul_apply, smul_eq_mul, hf₀'] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]

end GlobalTheory.RealLift.VacBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExchangeIndependentCompletionStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_completion : ∀ (E M : Type) [Field E] [AddCommGroup M] [Module E M] (n d : ℕ) (v : Fin n → M) (w : Fin d → M), LinearIndependent E v → LinearIndependent E w → (∀ k, v k ∈ Submodule.span E (Set.range w)) → ∃ K : Finset (Fin d), n + K.card = d ∧ LinearIndependent E (Sum.elim v fun k : K => w k) := by
  first | exact @GlobalTheory.exchange_independent_completion | exact GlobalTheory.exchange_independent_completion | (intros; apply GlobalTheory.exchange_independent_completion <;> assumption)
end

