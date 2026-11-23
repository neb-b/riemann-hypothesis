module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrame
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameOperators

open Formalism.L2.SG.PackageTie

section HS

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

omit [FiniteDimensional ℂ Wp] in
theorem norm_hsEmb_sq_sum (A : Wq →L[ℂ] Wp) :
    ‖hsEmb A‖ ^ 2 = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [hsEmb]

theorem sum_norm_sq_indep {ι ι' : Type} [Fintype ι] [Fintype ι'] (A : Wq →L[ℂ] Wp)
    (e : OrthonormalBasis ι ℂ Wq) (e' : OrthonormalBasis ι' ℂ Wq) :
    ∑ i, ‖A (e i)‖ ^ 2 = ∑ i, ‖A (e' i)‖ ^ 2 := by
  have : CompleteSpace Wq := FiniteDimensional.completeSpace ℂ Wq
  have : CompleteSpace Wp := FiniteDimensional.completeSpace ℂ Wp

  have key : ∀ {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ Wq),
      ∑ i, ‖A (b i)‖ ^ 2 = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)‖ ^ 2 := by
    intro κ _ b
    calc ∑ i, ‖A (b i)‖ ^ 2
        = ∑ i, ∑ k, ‖inner ℂ (stdOrthonormalBasis ℂ Wp k) (A (b i))‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact ((stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (A (b i))).symm
      _ = ∑ k, ∑ i, ‖inner ℂ (stdOrthonormalBasis ℂ Wp k) (A (b i))‖ ^ 2 := Finset.sum_comm
      _ = ∑ k, ∑ i, ‖inner ℂ ((ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)) (b i)‖ ^ 2 := by
          simp only [ContinuousLinearMap.adjoint_inner_left]
      _ = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ Wp k)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact b.sum_sq_norm_inner_left _
  rw [key e, key e']

theorem norm_hsEmb_conj (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    ‖hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq)))‖ = ‖hsEmb A‖ := by
  have h2 : ‖hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq)))‖ ^ 2 = ‖hsEmb A‖ ^ 2 := by
    rw [norm_hsEmb_sq_sum, norm_hsEmb_sq_sum]
    have hU : ∀ i, ‖((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))) (stdOrthonormalBasis ℂ Wq i)‖ =
        ‖A (((stdOrthonormalBasis ℂ Wq).map U'.symm) i)‖ := by
      intro i
      simp [OrthonormalBasis.map_apply]
    simp_rw [hU]
    exact sum_norm_sq_indep A _ _
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

def opOf (x : HS Wq Wp) : Wq →L[ℂ] Wp :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (x i)

omit [FiniteDimensional ℂ Wp] in
theorem opOf_apply (x : HS Wq Wp) (e : Wq) :
    opOf x e = ∑ i, inner ℂ (stdOrthonormalBasis ℂ Wq i) e • x i := by
  simp [opOf]

omit [FiniteDimensional ℂ Wp] in
theorem hsEmb_opOf (x : HS Wq Wp) : hsEmb (opOf x) = x := by
  ext j
  simp [hsEmb, opOf_apply, orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Wq).orthonormal]

omit [FiniteDimensional ℂ Wp] in
theorem opOf_hsEmb (A : Wq →L[ℂ] Wp) : opOf (hsEmb A) = A := by
  ext e
  rw [opOf_apply]
  conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [hsEmb, map_sum, map_smul]

def opOfL : HS Wq Wp →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun := opOf
  map_add' x y := by
    ext e
    simp [opOf_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext e
    simp [opOf_apply, Finset.smul_sum, smul_comm c]

def conjOp (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp) where
  toFun A := (U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))
  map_add' A B := by
    ext e
    simp
  map_smul' c A := by
    ext e
    simp

def conjL (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) : HS Wq Wp →ₗᵢ[ℂ] HS Wq Wp where
  toLinearMap := hsEmb ∘ₗ conjOp U U' ∘ₗ opOfL
  norm_map' x := by
    show ‖hsEmb ((U : Wp →L[ℂ] Wp).comp ((opOf x).comp (U'.symm : Wq →L[ℂ] Wq)))‖ = ‖x‖
    rw [norm_hsEmb_conj, hsEmb_opOf]

theorem conjL_hsEmb (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (A : Wq →L[ℂ] Wp) :
    conjL U U' (hsEmb A) = hsEmb ((U : Wp →L[ℂ] Wp).comp (A.comp (U'.symm : Wq →L[ℂ] Wq))) := by
  show hsEmb (conjOp U U' (opOf (hsEmb A))) = _
  rw [opOf_hsEmb]
  rfl

theorem norm_tsum_conj {ι : Type*} (U : Wp ≃ₗᵢ[ℂ] Wp) (U' : Wq ≃ₗᵢ[ℂ] Wq) (k : ℂ) (x : ι → HS Wq Wp) :
    ‖∑' s, k • conjL U U' (x s)‖ = ‖k‖ * ‖∑' s, x s‖ := by

  have hmap : (∑' s, conjL U U' (x s)) = conjL U U' (∑' s, x s) := by
    have h : ((conjL U U').toLinearIsometryEquiv rfl).toContinuousLinearEquiv (∑' s, x s) =
        ∑' s, ((conjL U U').toLinearIsometryEquiv rfl).toContinuousLinearEquiv (x s) :=
      ContinuousLinearEquiv.map_tsum _
    simpa using h.symm
  rw [tsum_const_smul'', hmap, norm_smul, LinearIsometry.norm_map]

end HS

end Formalism.L2.SG.Pf.RowForm.ClassFrameOperators

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def ClassFrameU : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ,
        Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s.1 =
          (ζ * (((Real.sqrt ((bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
              (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0'))⁻¹ : ℝ) : ℂ) *
            Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
            ((U : X.Vpi u →L[ℂ] X.Vpi u).comp
              ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)).comp
                (U'.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

theorem classFrameC_of
    (hU : ClassFrameU X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hs⟩ := hU R ρ
  set B := bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq with hB
  set r : ℝ := (Real.sqrt (B.c0 * B.c0'))⁻¹ with hr

  have hsum : (∑' s : LiftT X Y u u' κ R ρ, liftVec X Y u u' s.1) =
      ∑' s : LiftT X Y u u' κ R ρ, (ζ * (r : ℂ)) • ClassFrameOperators.conjL U U'
        ((((Formalism.L2.SG.TermOp.wt s.1 : ℝ) : ℂ) * Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
          Formalism.L2.SG.PackageTie.hsEmb
            (Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) := by
    congr 1
    funext s
    unfold liftVec
    rw [hs s]
    simp only [map_smul, ClassFrameOperators.conjL_hsEmb, smul_smul]
    congr 1
    ring
  rw [hsum, ClassFrameOperators.norm_tsum_conj, norm_mul, hζ, one_mul, mul_pow]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hr, inv_pow, Real.sq_sqrt hc]

def ClassFrameOO : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ s : LiftT X Y u u' κ R ρ,
        Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                  ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) • Formalism.L2.SG.TermOp.OOt s.1 =
          (ζ * Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) •
            ((U : X.Vpi u →L[ℂ] X.Vpi u).comp
              ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)).comp
                (U'.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

theorem classFrame_scl (hV : 0 < X.volK2) :
    Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 =
      (Real.sqrt ((bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
        (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0'))⁻¹ := by
  simp only [Formalism.L2.SG.TermOp.scl]
  exact Formalism.L2.SG.MassDataConc.scaled_volume_level_subgroup X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ) hV
    (Formalism.L2.SG.MassDataConc.anOf (Y.tO u u') 0 0 0 0 0 0 0 0 0 0 ⟨0, 0⟩)

theorem classFrameU_of (hOO : ClassFrameOO X Y u u' vR i0 i0' νq κ) (hV : 0 < X.volK2) :
    ClassFrameU X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hs⟩ := hOO R ρ
  refine ⟨U, U', ζ, hζ, fun s => ?_⟩
  simp only [Formalism.L2.SG.TermOp.ampN]
  rw [hs s, ← classFrame_scl (hb := hb) (X0 := X0) (ψ := ψ) (sd := sd) (C := C) (Th := Th) (Q := Q) (M := M)
    (δ := δ) (hV := hV), smul_smul]
  congr 1
  ring

theorem classFrameC_of_OO (hOO : ClassFrameOO X Y u u' vR i0 i0' νq κ) (hV : 0 < X.volK2)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ := classFrameC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ
  (classFrameU_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ hOO hV) hc

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.GmapInvOf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ScalT

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem gmap_mul (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_one (L : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inv_of {a : S.V ≃ₗ[E] S.V} {L L' : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap a L' = L) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ L = L' := by
  rw [← h, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem xflag_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  simp only [Xflag, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.Xa, mapFlag, Submodule.map_span, Set.image_image]
  rfl

theorem z_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).fl.z = γ F.fl.z := by
  simp only [mapLF, dif_pos hγ, mapFlag]

theorem isPair_quot {T T' : E} (Λ Λ' : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (γ₁ γ₂ : S.V ≃ₗ[E] S.V) (h₁ : γ₁ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h₂ : γ₂ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hl₁ : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hl₂ : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (hι : IotaCompat Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g) :
    IsPair Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem h₂ ((Formalism.HermitianLatticesTheory.isom S.hT).inv_mem h₁), ?_⟩, fun j => ?_, ?_, hι⟩
  · rw [gmap_mul, gmap_inv_of hl₁, hl₂]
  · rw [xflag_mapLF γ₁ h₁, xflag_mapLF γ₂ h₂, ← Submodule.map_comp]
    congr 1
    ext x
    simp
  · rw [z_mapLF γ₁ h₁, z_mapLF γ₂ h₂]
    simp

end Gen

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def LiftIotaC : Prop :=
  ∀ s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic →
    (Y.tO u u').rowOf s₁ = (Y.tO u u').rowOf s₂ →
      IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D)

variable (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem scalTC_of (hκ : Formalism.L2.SG.DataInst.RowLabel κ) (hι : LiftIotaC X Y u u')
    (hg : ∀ i, 3 ≤ D.host.g i ∧ Formalism.L2.SG.LemmaN.Unram D.host.E (D.host.g i)) :
    ScalTC X Y u u' κ := by
  intro s₁ s₂ hG₁ hG₂ hn₁ hn₂ hrow
  have hG₁' : s₁.G ≠ 0 := fun h => hG₁ (by show Formalism.L2.SG.TermOp.Gt s₁ = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hG₂' : s₂.G ≠ 0 := fun h => hG₂ (by show Formalism.L2.SG.TermOp.Gt s₂ = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hι' := hι s₁ s₂ hG₁' hG₂' hn₁ hn₂ hrow
  rw [hκ _ _ ⟨hn₁, hG₁'⟩ ⟨hn₂, hG₂'⟩]
  change (s0T s₁ s₂ = 1 ∧ scalT s₁ s₂) ↔ _
  have hrow' : rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ := hrow
  obtain ⟨l₁, m₁, l₁', m₁', c₁⟩ := s₁
  obtain ⟨l₂, m₂, l₂', m₂', c₂⟩ := s₂
  have hl : l₁ = l₂ := congrArg (fun q => q.1.1) hrow'
  have hl' : l₁' = l₂' := congrArg (fun q => q.2.1.1) hrow'
  subst hl hl'
  set s₁ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l₁, m₁, l₁', m₁', c₁⟩ with hs₁
  set s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := ⟨l₁, m₂, l₁', m₂', c₂⟩ with hs₂
  have hRL : IsRowLat D (X.Fu u) l₁ := (Y.rowsOK u).1 l₁ m₁
  have hP : IsPair l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) :=
    isPair_quot l₁ l₁' (gS D) (lf D (X.Fu u)) (lf D (X.Fu u')) s₁.lin s₂.lin s₁.rep.2.2.1 s₂.rep.2.2.1
      s₁.rep.2.2.2.1 s₂.rep.2.2.2.1 hι'
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) l₁ hRL
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) l₁ hRL).1
  let x₁ : Carrier (PD D l₁ (lf D (X.Fu u)) u') := ⟨s₁.frame, s₁.rep.2.2.2.2⟩
  let x₂ : Carrier (PD D l₁ (lf D (X.Fu u)) u') := ⟨s₂.frame, s₂.rep.2.2.2.2⟩
  have gv : ∀ x : Carrier (PD D l₁ (lf D (X.Fu u)) u'),
      Gt l₁ (lf D (X.Fu u)) (PD D l₁ (lf D (X.Fu u)) u') (TermDef.mk _ _ _ x) = Gval (lf D (X.Fu u)) x.1 := by
    intro x
    exact hGF _ _ ((hEq _ _).1 (Quot.out_eq (TermDef.mk l₁ (lf D (X.Fu u)) (PD D l₁ (lf D (X.Fu u)) u') x)))
  have hx₁ : Gval (lf D (X.Fu u)) x₁.1 ≠ 0 := by rw [← gv]; exact hG₁'
  have hx₂ : Gval (lf D (X.Fu u)) x₂.1 ≠ 0 := by rw [← gv]; exact hG₂'
  have hs0 : s0T s₁ s₂ = Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k := by
    unfold s0T
    exact if_pos ⟨rfl, rfl⟩
  have hsc : scalT s₁ s₂ ↔ (Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1 ∧
      IsScalar l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹)) := by
    unfold scalT
    exact ⟨fun h => h.2, fun h => ⟨⟨rfl, rfl⟩, h⟩⟩
  rw [hs0, hsc]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨⟨l₁, m₁, x₁, x₂, hx₁, hx₂, s₂.lin * s₁.lin⁻¹, hP⟩, rfl, rfl, h1, h2⟩
  · rintro ⟨⟨pl, pm, y₁, y₂, hy₁, hy₂, β, hβ⟩, hp₁, hp₂, hsp⟩
    have hp₁' : (Term.mk pl pm (TermDef.mk _ _ _ y₁) : Term D u u' (X.Fu u) (Y.what₂ u)) =
        Term.mk l₁ m₁ (TermDef.mk _ _ _ x₁) := hp₁
    obtain ⟨hpl, e₁⟩ := Term.mk.inj hp₁'
    subst pl
    have hp₂' : (Term.mk l₁ pm (TermDef.mk _ _ _ y₂) : Term D u u' (X.Fu u) (Y.what₂ u)) =
        Term.mk l₁ m₂ (TermDef.mk _ _ _ x₂) := hp₂
    obtain ⟨-, e₂⟩ := Term.mk.inj hp₂'
    have r₁ := (hEq y₁ x₁).1 (eq_of_heq e₁)
    have r₂ := (hEq y₂ x₂).1 (eq_of_heq e₂)
    have hSE := Formalism.L2.SG.Closed.ScalarEquiv_holds D u u' (X.Fu u) l₁ hRL
    have hRF := Formalism.L2.SG.Closed.ScalarRepFree_holds D u u' (X.Fu u) l₁ hRL
    have a1 : Formalism.L2.SG.Corank.ScalRelD D u' (X.Fu u) l₁ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ := ⟨β, hβ, hsp.1, hsp.2⟩
    have a2 := hRF ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ⟨x₂, hx₂⟩ r₂ a1
    have a3 := hRF ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩ ⟨x₁, hx₁⟩ r₁ (hSE.symm a2)
    obtain ⟨β', hβ', h1, h2⟩ := hSE.symm a3
    have hB := Formalism.L2.SG.Closed.BetaFree_holds D u u' hg (X.Fu u) l₁ hRL x₁ x₂ hx₁ hx₂ β' _ hβ' hP
    have e0 : Lat.s0 l₁ (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1 := hB.1 ▸ h1
    exact ⟨e0, e0, hB.2.1 h2⟩

end Formalism.L2.SG.Pf.RowForm.ScalT
end
end

