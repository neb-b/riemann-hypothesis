module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DoublingTheta

section Matrices

variable (R : Type) [CommRing R] (m n : ℕ)

def inL : Matrix (Fin (m + n)) (Fin m) R :=
  (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin n) (Fin m) R)).submatrix finSumFinEquiv.symm id

def inR : Matrix (Fin (m + n)) (Fin n) R :=
  (Matrix.fromRows (0 : Matrix (Fin m) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix finSumFinEquiv.symm id

variable {R m n}

theorem inL_map {R' : Type} [CommRing R'] (f : R →+* R') : (inL R m n).map f = inL R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.one_apply]
    split_ifs <;> simp
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, map_zero]

theorem inR_map {R' : Type} [CommRing R'] (f : R →+* R') : (inR R m n).map f = inR R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.zero_apply, map_zero]
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.one_apply]
    split_ifs <;> simp

theorem mul_inL {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inL R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inL, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem mul_inR {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inR R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inR, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem blkMat_inL (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inL R m n = inL R m n * a := by
  rw [blkMat, inL, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

theorem blkMat_inR (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inR R m n = inR R m n * b := by
  rw [blkMat, inR, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

variable [StarRing R]

theorem inL_inL : (inL R m n)ᴴ * inL R m n = 1 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inL, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inR : (inR R m n)ᴴ * inR R m n = 1 := by
  rw [mul_inR]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inL : (inR R m n)ᴴ * inL R m n = 0 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR]

end Matrices

variable {D : D7}

def sumDec (V W : HSp D) : GlobalTheory.MixModel.OrthDec (sumSp V W) V W where
  iA := inL D.host.E V.rank W.rank
  iB := inR D.host.E V.rank W.rank
  isoA := by
    change (inL D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = V.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inL_inL, Matrix.one_mul]
  isoB := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inR D.host.E V.rank W.rank = W.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inR, ← Matrix.mul_assoc, inR_inR, Matrix.one_mul]
  orth := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = 0
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inR_inL, Matrix.zero_mul]
  rank_add := rfl

theorem sumDec_jA (V W : HSp D) : (sumDec V W).jA = inL (AE D) V.rank W.rank := inL_map (incA D)

theorem sumDec_jB (V W : HSp D) : (sumDec V W).jB = inR (AE D) V.rank W.rank := inR_map (incA D)

theorem sumDec_emb (V W : HSp D) (g : GA D V) (g' : GA D W) : (sumDec V W).emb (g, g') = ioSum V W (g, g') := by
  refine GlobalTheory.MixModel.mt_injective _ ?_
  have hA : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jA = HMul.hMul (sumDec V W).jA (mt V g) := by
    rw [sumDec_jA]; exact blkMat_inL (mt V g) (mt W g')
  have hB : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jB = HMul.hMul (sumDec V W).jB (mt W g') := by
    rw [sumDec_jB]; exact blkMat_inR (mt V g) (mt W g')
  rw [GlobalTheory.MixModel.OrthDec.mt_emb, ← hA, ← hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
    GlobalTheory.MixModel.OrthDec.sum_eq_one, Matrix.mul_one]

theorem boxS_apply (A B : HSp D) (f : WO A B → ℂ) (f' : WO (negSp A) B → ℂ) (x : WO (dblSp A) B) :
    (sumDec A (negSp A)).boxS B f f' x = f (resL A B x) * f' (resR A B x) := by
  rw [GlobalTheory.MixModel.OrthDec.boxS, GlobalTheory.MixModel.OrthDec.resS_apply, sumDec_jA, sumDec_jB]
  exact congrArg₂ (· * ·) (congrArg f (mul_inL x)) (congrArg f' (mul_inR x))

theorem thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ThetaClause ψ A B χB om omh := by
  intro D ψ A B χA χB om omh hom homh f₁ f₂ h₁ h₂
  refine ⟨_root_.GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hom.std f₁ f₂ h₁ h₂, fun g₁ g₂ h => ?_⟩
  obtain ⟨hθ, om', hom', hact⟩ := _root_.GlobalTheory.NegWeil.exists_neg_datum D ψ A B χA χB om hom
  have hT := _root_.GlobalTheory.TensorSrc.tensorSource D ψ hom.std (sumSp A (negSp A)) A (negSp A) (sumDec A (negSp A)) B
  have hh : IsWeilDatumO ψ (sumSp A (negSp A)) B (χA * χA⁻¹) χB omh := by rw [mul_inv_cancel]; exact homh
  have key := hT.om_box χA χA⁻¹ χB omh om om' hh hom hom' g₁ ((negEquiv A).symm g₂) h f₁ _ h₁ (hθ f₂ h₂)
  rw [hact _ h f₂ h₂, sumDec_emb, io_eq_ioSum, MulEquiv.apply_symm_apply] at key
  have e : (sumDec A (negSp A)).boxS B f₁ (fun x => conj (f₂ (-x))) = delta A B f₁ f₂ :=
    funext fun x => boxS_apply A B _ _ x
  have main : omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
      (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) := by
    rw [← e]
    refine key.trans (funext fun x => (boxS_apply A B _ _ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨main, ?_⟩
  have zL : resL A B 0 = 0 := rfl
  have zR : resR A B 0 = 0 := rfl
  rw [thetaKO, main]
  simp only [thetaKO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul, zL, zR, neg_zero]
  ring

end GlobalTheory.DoublingTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalDoubleCosetRepresentativeBounds
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge.RepsOnto
open GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL

theorem val_unif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

theorem denseRange_toLoc {E k : Type} [Field E] [Field k] [TopologicalSpace k] {ι : E →+* k} (hι : DenseRange ι)
    {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) : DenseRange (toLoc ι e e') := by
  have h1 : DenseRange (Pi.map fun (_ : A) => Pi.map fun (_ : B) => (ι : E → k)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hι
  refine Dense.mono ?_ h1
  rintro _ ⟨M, rfl⟩
  refine ⟨Matrix.toLin' ((Matrix.of M).submatrix e.symm e'.symm), ?_⟩
  rw [toLoc_eq, LinearMap.toMatrix'_toLin']
  ext i l
  simp


open GlobalTheory.LatClass GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice in
theorem exists_bounded_rep : ∀ (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ j c (h : j + 1 + c = s) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1 + 1)) k),
    (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1 + 1) 1,
      GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) →
    ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
    flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 →
    ∃ g₁ : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k,
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g₁ =
        DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h' ∧
      ∀ κ ∈ ((W.T s R).lev (j + 1) (c + 1) (by omega)).J,
        latOf 1 ≤ latOf (g₁ * κ) ∧ ∀ y ∈ latOf (g₁ * κ), ((W.ϖ : k) ^ (j + 1)) • y ∈ latOf 1 := by
  intro R k _ _ _ _ s W _ _ ν hν j c h g hr h' hf
  haveI := hν.1
  have hϖ := val_unif W.unif
  have hb : ∀ j c h, latOf ((W.T s R).bas j c h) = latOf 1 := fun _ _ _ => rfl
  have H : (∀ j c h x, (W.T s R).Phi j c h x ≠ 0 → IntM x) ∧
      (∀ j c h x y, MaxM y → (W.T s R).Phi j c h (x + y) = (W.T s R).Phi j c h x) ∧
      ∀ j c h, ((W.T s R).lev j c h).J ≤ KO k _ :=
    GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s _ _ _ _ W.δ W.tame W.η _ _ (fun _ _ _ => rfl)
  obtain ⟨hs, hp, hJ⟩ := H
  obtain ⟨r, hr, e', z', he', hz', hl⟩ := hr
  rw [lat_bas hb, ← nfBasis_one] at hl
  obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c W.ψ ν _ _ g h' hf r hr)
  obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ W.cond he' hz'
    (hl ▸ om_supp (hs _ _ _) (r * g) h') (hl ▸ om_per hϖ (hp _ _ _) (r * g) h') h0
  refine ⟨r₂ * h', ((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨r₂, hr₂, 1, one_mem _, (mul_one _).symm⟩).symm, fun κ hκ => ?_⟩
  rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ _ _ _ hκ)), mul_one, hl₂]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [mem_latOf_one] at hy
    exact mem_normal.2 ⟨fun r => sub_mem (hy _) (mul_mem (hy _) (hz r)),
      fun i => pow_mono hϖ (he i).2 (mem_pow_zero.2 (hy _))⟩
  · obtain ⟨h1, h2⟩ := mem_normal.1 hy
    have h3 : ∀ i, (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) * y (.inr i) ∈ 𝒪[k] := fun i =>
      mem_pow_zero.1 (zpow_mul_mem_pow.2 (pow_mono hϖ (by have := he i; omega) (h2 i)))
    have h4 : (W.ϖ : k) ^ ((j + 1 : ℕ) : ℤ) ∈ 𝒪[k] := mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by omega))
    rw [mem_latOf_one, ← zpow_natCast]
    rintro (r | i)
    · convert add_mem (mul_mem h4 (h1 r)) (mul_mem (h3 0) (hz r)) using 1
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    · exact h3 i

theorem exists_toLocGL_mem : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A : Type) [Fintype A] [DecidableEq A] (a : ℕ) (e : A ≃ Fin a) (U : Set (GL A k)),
    IsOpen U → U.Nonempty → ∃ γ : (Fin a → E) ≃ₗ[E] (Fin a → E), toLocGL ι e γ ∈ U := by
  intro E k _ _ _ _ _ ι hι A _ _ a e U hU ⟨g₀, hg₀⟩
  haveI : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hS : IsOpen {M : Matrix A A k | M.det ≠ 0} := isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  let F : {M : Matrix A A k | M.det ≠ 0} → GL A k := fun M => GeneralLinearGroup.mkOfDetNeZero M.1 M.2
  have hF : Continuous F := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have : (fun M => ((F M)⁻¹ : GL A k).val) = fun M => (M.1.det)⁻¹ • M.1.adjugate := by
      funext M
      rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
      rfl
    rw [this]
    exact ((continuous_subtype_val.matrix_det).inv₀ fun M => M.2).smul continuous_subtype_val.matrix_adjugate
  have hV := hS.isOpenMap_subtype_val _ (hU.preimage hF)
  have hne : (Subtype.val '' (F ⁻¹' U)).Nonempty := by
    refine ⟨_, ⟨g₀.val, g₀.det_ne_zero⟩, ?_, rfl⟩
    have : F ⟨g₀.val, g₀.det_ne_zero⟩ = g₀ := Units.ext rfl
    rw [Set.mem_preimage, this]
    exact hg₀
  obtain ⟨x, M, hM, hx⟩ := (denseRange_toLoc hι e e).exists_mem_open hV hne
  have hd : LinearMap.det x ≠ 0 := by
    intro h0
    have h1 := M.2
    rw [Set.mem_setOf_eq, hx, toLoc_eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self,
      LinearMap.det_toMatrix', h0, map_zero] at h1
    exact h1 rfl
  have hbij : Function.Bijective x := (Module.End.isUnit_iff x).1 ((LinearMap.isUnit_iff_isUnit_det x).2 hd.isUnit)
  refine ⟨LinearEquiv.ofBijective x hbij, ?_⟩
  have : toLocGL ι e (LinearEquiv.ofBijective x hbij) = F M := Units.ext hx.symm
  rw [this]
  exact hM

theorem exists_toLoc_ne_zero : ∀ (E k : Type) [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : E →+* k), DenseRange ι → ∀ (A B : Type) [Fintype A] [Fintype B] (a b : ℕ) (e : A ≃ Fin a) (e' : B ≃ Fin b)
    (f : Matrix A B k → ℂ), IsLocallyConstant f → f ≠ 0 → ∃ x : (Fin b → E) →ₗ[E] (Fin a → E), f (toLoc ι e e' x) ≠ 0 := by
  intro E k _ _ _ _ _ ι hι A B _ _ a b e e' f hf hne
  exact (denseRange_toLoc hι e e').exists_mem_open (hf {z | z ≠ 0}) (Function.ne_iff.1 hne)

theorem toLoc_mulVec {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] {a : ℕ} (e : A ≃ Fin a)
    (x : (Fin a → E) →ₗ[E] (Fin a → E)) (y : Fin a → E) :
    (toLoc ι e e x *ᵥ fun i => ι (y (e i))) = fun i => ι (x y (e i)) := by
  funext i
  rw [toLoc_eq, ← LinearMap.toMatrix'_mulVec]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul, map_apply, submatrix_apply]
  exact Equiv.sum_comp e fun l => ι (LinearMap.toMatrix' x (e i) l) * ι (y l)

theorem bounds_of_isGL : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (P : HeightOneSpectrum (𝓞 X.E)) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ),
    IsCompl P (qOf P) ι ϖ → P ∉ Pr.vGs → ∀ (j c n : ℕ) (γ : AutY X R j) (g' : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι γ g' → latOf 1 ≤ latOf g' → (∀ y ∈ latOf g', ((ϖ : k) ^ n) • y ∈ latOf 1) →
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ n) • γ x ∈ lamYat (Pr := Pr) (R := R) j P := by
  intro X Pr R P k _ _ _ _ ι ϖ hC hP j c n γ g' ⟨e, _, hg⟩ h1 h2 x hx
  have hmem : ∀ y, y ∈ lamYat (Pr := Pr) (R := R) j P ↔ (fun i => ι (y (e i))) ∈ latOf (1 : GL _ k) := fun y => by
    unfold lamYat LocE.lamY LocE.sclLat stdAt
    rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice, mem_latOf_one]
    simp only [hC.int]
    rw [e.surjective.forall]
    simp [LocE.scE]
  obtain rfl : g' = toLocGL ι e γ := Units.ext hg
  rw [hmem] at hx
  refine ⟨(hmem _).2 (mem_latOf_one.2 ?_), (hmem _).2 ?_⟩
  · have h3 : ∀ i, (toLoc ι e e γ.symm.toLinearMap *ᵥ fun i => ι (x (e i))) i ∈ 𝒪[k] := h1 hx
    rw [toLoc_mulVec] at h3
    exact h3
  · have h3 : (toLocGL ι e γ).val *ᵥ (fun i => ι (x (e i))) ∈ latOf (toLocGL ι e γ * 1) := (mulVec_mem_latOf _).2 hx
    rw [mul_one] at h3
    have h4 := h2 _ h3
    change (ϖ : k) ^ n • (toLoc ι e e γ.toLinearMap *ᵥ fun i => ι (x (e i))) ∈ _ at h4
    rw [toLoc_mulVec, hC.unif] at h4
    convert h4 using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    rfl

theorem ordX_exists (R : Ranks) (j : ℕ) : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), IsOrd xPos e := by
  have hN : R.k + j + j * R.t + 0 = R.N j := by simp only [Ranks.N]; ring
  refine ⟨(Equiv.sumEmpty _ (Fin 0)).symm.trans (ordY R.k R.t j 0 _ hN), fun a => ?_⟩
  have := ordY_isOrd R.k R.t j 0 _ hN (Sum.inl a)
  simpa [yPos] using this

end GlobalTheory.TwBridge.RepsOnto


open GlobalTheory.TwBridge.RepsOnto GlobalTheory.SymBridge GlobalTheory.TwBridge.MatGL in
theorem GlobalTheory.TwBridge.repsOnto : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g → (∃ r ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j)) (c + 1 + 1) 1, GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.IsNormalRep (W.T s R) W.ϖ j (c + 1) (by omega) (r * g)) → ∀ h' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g h' ≠ 0 → ∃ γ : AutY X R (j + 1), (∃ g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k, IsGL ι γ g' ∧ DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J g' = DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J h') ∧ (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) ∧ FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hI j c h al g hg hr h' hf
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨g₁, hdc, hbd⟩ := exists_bounded_rep R k s W ν hν j c h g hr h' hf
  set J := ((W.T s R).lev (j + 1) (c + 1) (by omega)).J with hJ
  have hreg : (W.T s R).Regular := GlobalTheory.StepData.Chain.ofTwist_regular _ _ _ _ _
  have hlaws : (W.T s R).Laws := GlobalTheory.StepData.Chain.ofTwist_laws _ _ _ W.unr _ _
  have hJo := (hreg.2.2 (j + 1) (c + 1) (by omega)).1
  have hm := hA.steps
  have hN : R.k + (j + 1) + (j + 1) * R.t + (c + 1) = R.N (j + 1) + cOf R (j + 1) := by
    have e2 : R.N (j + 1) = R.k + (j + 1) + (j + 1) * R.t := by simp only [Ranks.N]; ring
    rw [e2]; simp only [cOf]; rw [hm]; omega
  have ho : IsOrdY (ordY R.k R.t (j + 1) (c + 1) _ hN) := by
    have := ordY_isOrd R.k R.t (j + 1) (c + 1) _ hN
    have e2 : R.k + (j + 1) + (j + 1) * R.t = R.N (j + 1) := by simp only [Ranks.N]; ring
    rwa [e2] at this
  obtain ⟨γ, hγ⟩ := exists_toLocGL_mem X.E k ι hA.compl.dense _ _ (ordY R.k R.t (j + 1) (c + 1) _ hN)
    {x | g₁⁻¹ * x ∈ J} (hJo.preimage (continuous_const.mul continuous_id)) ⟨g₁, by simp [J.one_mem]⟩
  set g' := toLocGL ι (ordY R.k R.t (j + 1) (c + 1) _ hN) γ with hg'
  have hgl : IsGL ι γ g' := ⟨_, ho, rfl⟩
  have hκ : g₁⁻¹ * g' ∈ J := hγ
  have hdc' : DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J g' =
      DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) J h' := by
    rw [← hdc]
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨1, one_mem _, (g₁⁻¹ * g')⁻¹, inv_mem hκ, by group⟩
  obtain ⟨hb1, hb2⟩ := hbd _ hκ
  rw [mul_inv_cancel_left] at hb1 hb2
  have hbd' := bounds_of_isGL X Pr R P.1 k ι W.ϖ hA.compl hA.nmem (j + 1) (c + 1) (j + 1) γ g' hgl hb1 hb2
  refine ⟨γ, ⟨g', hgl, hdc'⟩, hbd', ?_⟩
  have hfl : flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
    have hT := hlaws.1 j (c + 1) (by omega)
    exact (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (by omega) hT rfl hdc'.symm).1 hf
  have hSB := GlobalTheory.RootEx.opE_mem_SB 1 W.ψ ν (GlobalTheory.SplitWeil.om_mem_SB ((W.T s R).mu (j + 1)) g g'
    (hreg.1 j (c + 1) (by omega)))
  obtain ⟨e', he'⟩ := ordX_exists R j
  obtain ⟨e, he⟩ := ordX_exists R (j + 1)
  obtain ⟨x, hx⟩ := exists_toLoc_ne_zero X.E k ι hA.compl.dense _ _ _ _ e e'
    (flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g') hSB.1 hfl
  obtain ⟨A₀, B₀, hAB⟩ := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA j c h (L.h j al P) γ g g' hg hgl
    (hL.boundQ j al P hA.nmem) hbd' (hL.depthQ' P hA.nmem)
  refine ⟨A₀, B₀, fun A' B' h1 h2 hz => hx ?_⟩
  rw [hAB A' B' h1 h2 e' e he' he x]
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletions
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OrthIsom

open scoped TensorProduct

theorem mul_inv_mem_UJ {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R)
    (β β' : GL (Fin n) R) (h : Formalism.UG.cT σ β'.1 * J * β'.1 = Formalism.UG.cT σ β.1 * J * β.1) :
    β' * β⁻¹ ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1 = J
  calc Formalism.UG.cT σ (β' * β⁻¹).1 * J * (β' * β⁻¹).1
      = Formalism.UG.cT σ (β⁻¹).1 * (Formalism.UG.cT σ β'.1 * J * β'.1) * (β⁻¹).1 := by
        rw [Units.val_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by
        rw [h, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_iff_of_frames {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β β' : GL (Fin n) R)
    (H H' : Set (Fin n → R)) (h : ∀ y, y ∈ H ↔ ∀ i, ((β⁻¹).val *ᵥ y) i ∈ S)
    (h' : ∀ y, y ∈ H' ↔ ∀ i, ((β'⁻¹).val *ᵥ y) i ∈ S) (y : Fin n → R) :
    y ∈ H ↔ (β' * β⁻¹).val *ᵥ y ∈ H' := by
  rw [h, h', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (R : Type) [CommRing R] [Algebra F R]

theorem swap_symm_mem_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (g : GL (Fin n) (E ⊗[F] R)) (hg : g ∈ Formalism.UG.UPts σ J R) :
    Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g ∈ HR R σ J := by
  have h := Formalism.UG.Final.BCMem _ _ (Fin n) (Formalism.UG.sigR σ R) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)
    (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom
    (RingHom.ext fun x => ?_) (J.map (Formalism.UG.inclE R)) g hg
  · exact h
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a x => rfl

theorem swap_mulVec (g : GL (Fin n) (E ⊗[F] R)) (z : Fin n → R ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F R E
      (((Formalism.UG.bc (Algebra.TensorProduct.comm F R E).symm.toAlgHom.toRingHom g).val *ᵥ z) i)) =
      g.val *ᵥ fun i => Algebra.TensorProduct.comm F R E (z i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (Algebra.TensorProduct.comm F R E).apply_symm_apply (g.val i j)

end Alg

section Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_latHat_iff_swap (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → Af F ⊗[F] E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  have h1 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h
  simp only [AlgEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_of_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (g : GL (Fin n) (E ⊗[F] Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Af F))
    (h : ∀ y, y ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ g.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ') :
    ∃ b ∈ HR (Af F) σ J, ∀ w : Fin n → Af F ⊗[F] E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔ b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ' : Set (Fin n → E)) := by
  refine ⟨_, swap_symm_mem_HR (Af F) σ J g hg, fun w => ?_⟩
  rw [mem_latHat_iff_swap, mem_latHat_iff_swap, swap_mulVec]
  exact h _

end Swap

theorem exists_unitary_latHat : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)),
    IsSelfDualC A L → IsSelfDualC A L' →
    ∃ b ∈ HR (Af D.host.F) D.sp.cm.sig A.gram, ∀ w : Fin A.rank → TensorProduct D.host.F (Af D.host.F) D.host.E,
      w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L : Set (Fin A.rank → D.host.E)) ↔
        b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L' : Set (Fin A.rank → D.host.E)) := by
  intro D A L L' hL hL'
  obtain ⟨β, e, hβ⟩ := GlobalTheory.AdIsom.exists_orth hL
  obtain ⟨β', e', hβ'⟩ := GlobalTheory.AdIsom.exists_orth hL'
  refine exists_of_swap D.sp.cm.sig A.gram L L' (β' * β⁻¹) (mul_inv_mem_UJ _ _ β β' (hβ'.trans hβ.symm)) ?_
  rw [e, e']
  exact mem_iff_of_frames (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.OA D) β β' _ _ (GlobalTheory.AdIsom.mem_hat_lat β) (GlobalTheory.AdIsom.mem_hat_lat β')

end GlobalTheory.Core.Rk.OrthIsom
end
end

