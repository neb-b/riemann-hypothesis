module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSameDoubleCosetCompletionRowRepresentatives
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge.RepsInj

open GlobalTheory.TwBridge.Lev (dc_iff mem_par_iff phi)

theorem reps_injOn : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _hν _hc hA L G _hL hI j c h
  have sameDC (i d : ℕ) (hd : i + d = s + 1) (γ γ' : AutY X R i)
      (g g' : GL (XIx (Fin R.k) (Fin R.t) i ⊕ Fin d) k) (hg : IsGL ι γ g) (hg' : IsGL ι γ' g')
      (hmk : DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g =
        DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g') :
      SameDC (Pr := Pr) cst.sharp i P.1 γ γ' := by
    have hc : d = cOf R i := by
      have := hA.steps
      unfold cOf
      omega
    subst d
    obtain ⟨e, he, hg⟩ := hg
    obtain ⟨e', he', hg'⟩ := hg'
    have heq : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
    subst e'
    obtain rfl : g = phi ι e γ := Units.ext hg
    obtain rfl : g' = phi ι e γ' := Units.ext hg'
    let o := stdOrd (Fin R.k) (Fin R.t) i (cOf R i) hd
    have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := by
      intro g
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply,
        show (plainFrame (k := k) o).bas = 1 from rfl,
        show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
      simp
    have hJ : ∀ g, g ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        (reGL o).symm g ∈ (parahoric _ (Fin i × Fin R.t) W.δ W.tame).J := by
      intro g
      rw [← hconj]
      rfl
    have hmem : ∀ γ : AutY X R i, phi ι e γ ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        γ ∈ Jat (Pr := Pr) cst.sharp i P.1 := by
      intro γ
      rw [hJ, Jat, ite_eq_right hA.nmem]
      exact mem_par_iff hA.compl W.unif hd rfl he W.tame γ
    exact (dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _
      (fun u hu => (hJ u).2 (((parahoric _ (Fin i × Fin R.t) W.δ W.tame).reindex o).KOne_le hu))
      _ hmem γ γ').2 hmk
  rintro g₁ ⟨b, hb⟩ g₂ ⟨b', hb'⟩ hmk
  have hS := sameDC (j + 1) (c + 1) (by omega) _ _ g₁ g₂ hb hb' hmk
  have heq : L.h (j + 1) b P = L.h (j + 1) b' P := hI (j + 1) b b' P hS
  rw [← heq] at hb'
  obtain ⟨e₁, he₁, h₁⟩ := hb
  obtain ⟨e₂, he₂, h₂⟩ := hb'
  have he : e₁ = e₂ := by
    ext a
    exact (he₁ a).trans (he₂ a).symm
  subst he
  exact Units.ext (h₁.trans h₂.symm)

end GlobalTheory.TwBridge.RepsInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun.DblSplit

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

theorem blkGL_mem_diag (a : GL m A) : blkGL e (a, a) ∈ Formalism.UG.stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)

theorem keepsDiag_conj_iff (a : GL m A) (x : GL ι A) :
    KeepsDiag e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1 ↔ KeepsDiag e x.1 := by
  rw [← mem_stabGL_diagSub, ← mem_stabGL_diagSub, Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem det_leviMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let p : Formalism.UG.stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  let q : Formalism.UG.stabGL (diagSub A e) := ⟨x, mem_stabGL_diagSub.2 hx⟩
  change (leviGL e (p⁻¹ * q * p)).1.det = (leviGL e q).1.det
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem det_quotMat_conj (a : GL m A) {x : GL ι A} (hx : KeepsDiag e x.1) :
    (quotMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (quotMat e x.1).det := by
  have h1 := ((keepsDiag_conj_iff e a x).2 hx).det_eq
  rw [det_leviMat_conj e a hx, Units.val_mul, Units.val_mul, Matrix.det_units_conj', hx.det_eq] at h1
  have hu : IsUnit (leviMat e x.1).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [hx.det_eq] at this
    exact isUnit_of_mul_isUnit_left this
  exact (hu.mul_left_cancel h1).symm

omit [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] in
theorem quotMat_map {B : Type} [CommRing B] (f : A →+* B) (M : Matrix ι ι A) :
    quotMat e (M.map f) = (quotMat e M).map f := by
  ext i j; simp [quotMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

end Pure

theorem ordL_eq_neg_log {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (x : K) :
    ordL x = -WithZero.log (Valued.v x) := by
  unfold ordL
  split_ifs with h
  · simp [h]
  · conv_rhs => rw [← WithZero.coe_unzero h]
    rfl

theorem isHermND_dbl {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) : IsHermND σ (dblGram finSumFinEquiv J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
    simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [hJ.1]
  · rw [dblGram, det_blkMat]
    exact mul_ne_zero hJ.2 (by rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by simp)) hJ.2)

theorem exists_dbl_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n := (n + n))) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  intro F E _ _ _ _ _ σ hc n J hJ Q hQ L _ v w h hv hL e he
  have hQ' : IsHermND σ Q := hQ ▸ isHermND_dbl σ hJ
  obtain ⟨⟨a, ha, ea⟩, -⟩ := id he
  obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
  let φ := ConjPlace.complEquiv hc h hτ
  let β := Formalism.UG.bc (φ.symm : w.adicCompletion E →+* Fv F v) (blkGL finSumFinEquiv (a, a))
  have hβ : IsSplitBasis τ (sumLat finSumFinEquiv L L) β := by
    apply (ConjPlace.isFrameAt_iff hc h hτ β).1
    have heq : Formalism.UG.bc (φ : Fv F v →+* w.adicCompletion E) β =
        blkGL finSumFinEquiv (a, a) := by
      apply Units.ext
      exact Matrix.ext fun i j => φ.apply_symm_apply _
    rw [heq]
    exact _root_.GlobalTheory.LFun.isFrameAt_sumLat_blkGL E w n L a ha
  obtain ⟨f₀, ⟨⟨b, hb, e0⟩, hK⟩⟩ :=
    ConjPlace.exists_isSplitChart_of_basis hc hQ' (isSelfDualAt_dbl hQ hL) h hτ hβ
  have hk := hb.inv_mul_mem (_root_.GlobalTheory.LFun.isFrameAt_sumLat_blkGL E w n L a ha)
  have ef : ∀ g, f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹) g =
      (blkGL finSumFinEquiv (a, a))⁻¹ * locMat σ Q h g * blkGL finSumFinEquiv (a, a) := fun g => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, e0]; group
  have hP : ∀ p : siegelH (Fv F v) σ Q, KeepsDiag finSumFinEquiv (locMat σ Q h p).1 := fun p =>
    (mem_siegelOf.1 p.2).map _ (toCompl h)
  refine ⟨f₀.trans (MulAut.conj (b⁻¹ * blkGL finSumFinEquiv (a, a))⁻¹), fun g => ?_, fun y y' => ?_, fun g => ?_,
    fun p => ⟨?_, fun w' h' hne => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ hk,
      Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
    exact hK g
  · have h1 : locMat σ Q h (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (locMat σ J h y, locMat σ J h y') :=
      bc_blkGL finSumFinEquiv (toCompl h) _ _
    rw [ef, h1, ← map_inv, ← map_mul, ← map_mul, ea, ea]
    rfl
  · rw [ef, keepsDiag_conj_iff]
    refine ⟨fun hg => hP ⟨g, hg⟩, fun hg => ?_⟩
    obtain ⟨τ, hτ⟩ := SplitChart.exists_splitPrime_eq hc hv h
    refine GlobalTheory.Core.Rk.IwSplit.mem_siegelH_of_split hc hQ hJ.2 τ (mem_stabGL_diagSub.2 ?_)
    rw [ConjPlace.locMat_eq hc h hτ] at hg
    have h2 := hg.map _ ((ConjPlace.complEquiv hc h hτ).symm : w.adicCompletion E →+* Fv F v)
    convert h2 using 1
    exact Matrix.ext fun i j => ((ConjPlace.complEquiv hc h hτ).symm_apply_apply _).symm
  · rw [ef, det_leviMat_conj _ a (hP p)]
    change toCompl h (leviMat finSumFinEquiv (matHom _ σ Q p).1).det =
      (leviMat finSumFinEquiv ((matHom _ σ Q p).1.map (toCompl h))).det
    rw [leviMat_map, RingHom.map_det, RingHom.mapMatrix_apply]
  · obtain ⟨c, hcv, -, hcc, -⟩ := ConjPlace.exists_conj_chart hc hJ hL hne h h' he
    rw [ef, det_quotMat_conj _ a (hP p)]
    have h1 : (quotMat finSumFinEquiv (locMat σ Q h p).1).det =
        toCompl h (quotMat finSumFinEquiv (matHom _ σ Q p).1).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← quotMat_map]
      rfl
    have h2 := congrArg (fun y => Valued.v (toCompl h' y)) (sigR_det_quot_mul_aH hQ hJ.2 p)
    simp only [map_mul, map_one, ← hcc, hcv] at h2
    rw [h1, ordL_eq_neg_log, ordL_eq_neg_log, eq_inv_of_mul_eq_one_right h2, WithZero.log_inv]

end GlobalTheory.LFun.DblSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHypDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_scaled {E : Type} [Field E] [StarRing E] {n k l : Type} [Fintype n] (G : Matrix n n E)
    (A : Matrix n k E) (B : Matrix n l E) (α : k → E) (β : l → E) (x : k → n → E) (y : l → n → E)
    (hA : ∀ i a, A i a = α a * x a i) (hB : ∀ i b, B i b = β b * y b i) (a : k) (b : l) :
    (Aᴴ * G * B) a b = star (α a) * β b * (star (x a) ⬝ᵥ (G *ᵥ y b)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, hA, hB, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_sum {E : Type} [Field E] [StarRing E] {n k l m : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E)
    (hIJ : Iᴴ * G * J = 0) (hJI : Jᴴ * G * I = 0) :
    (I * P + J * Q)ᴴ * G * (I * P + J * Q) = Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q := by
  have e : (I * P + J * Q)ᴴ * G * (I * P + J * Q) =
      Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q + Pᴴ * (Iᴴ * G * J) * Q + Qᴴ * (Jᴴ * G * I) * P := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e, hIJ, hJI]
  simp

theorem gram_sum_zero {E : Type} [Field E] [StarRing E] {n k l m p : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E) (C : Matrix n p E)
    (hI : Iᴴ * G * C = 0) (hJ : Jᴴ * G * C = 0) :
    (I * P + J * Q)ᴴ * G * C = 0 := by
  have e : (I * P + J * Q)ᴴ * G * C = Pᴴ * (Iᴴ * G * C) + Qᴴ * (Jᴴ * G * C) := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [e, hI, hJ]
  simp

theorem exists_hypDec : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → (∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y) → (∀ (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0) → ∀ (L : HSp D), L.rank = 1 → (∀ i j, L.gram i j = star t * t * (VS D).hT (X.zu u) (X.zu u)) → ∀ (V₀ : HSp D) (o : OrthDec V₀ (D.sp.X 0) L), ∃ d : HypDec (D.sp.Y 0) V₀ D.R.rS, d.e = GlobalTheory.Core.SBesEx.eM X h t lam ∧ d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam ∧ d.i₀ = GlobalTheory.Core.SBesEx.i0M X h u tr.wt t o := by
  intro D X h u F₀ tr t lam ht hlam hiso hfr L hL hLg V₀ o
  have hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y) := fun x y =>
    (LinearMap.isSymm_def.1 (VS D).herm x y).symm
  have hs : ∀ a : Fin D.R.rS, star (scl t lam a) ≠ 0 := fun a =>
    star_ne_zero.2 (mul_ne_zero ht (pow_ne_zero _ hlam))
  set q : Fin (D.sp.X 0).rank → (VS D).V := fun i =>
    Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i) with hq
  have hE : ∀ i a, eM X h t lam i a = scl t lam a * cY X h (X.eX a) i := fun _ _ => rfl
  have hE' : ∀ i a, e'M X h t lam i a = (star (scl t lam a))⁻¹ * cY X h (X.fY a) i := fun _ _ => rfl
  have hQ : ∀ i a, qM X h tr.wt i a = (1 : D.host.E) * cY X h (q a) i := fun _ _ => (one_mul _).symm
  have hZ : ∀ i a, zM X h u t L i a = t * cY X h (X.zu u) i := fun _ _ => rfl
  have hzq : ∀ i, (VS D).hT (X.zu u) (q i) = 0 := by
    intro i
    rw [hsym, ← tr.wt_isom, tr.weight_z]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr, D7.zmOf, map_smul]
    rw [D.sp.zm_orth, smul_zero, star_zero]
  have hqq : ∀ i j, (VS D).hT (q i) (q j) = (D.sp.X 0).gram i j := by
    intro i j
    rw [← tr.wt_isom]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr]
    rw [D.sp.iXY_isom 0 (lt_of_lt_of_le two_pos D.R.two_le_m)]
    rfl
  have hQZ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * zM X h u t L = 0 := by
    ext a b
    rw [gram_scaled _ _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) hQ hZ, hiso, hsym, hzq]
    simp
  have hZQ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = 0 := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hQ, hiso, hzq]
    simp
  have hQQ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = (D.sp.X 0).gram := by
    ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hQ hQ, hiso, hqq]
    simp
  have hZZ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * zM X h u t L = L.gram := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) (fun _ => t) (fun _ => cY X h (X.zu u)) (fun _ => cY X h (X.zu u)) hZ hZ,
      hiso, hLg]
  refine ⟨⟨eM X h t lam, e'M X h t lam, i0M X h u tr.wt t o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE hE, hiso, X.ee]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE', hiso, X.ff]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE, hiso, hsym, X.ef, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      have := hs a
      rw [star_ne_zero] at this
      simp [this]
    · simp [hab, Ne.symm hab]
  · rw [i0M, gram_sum _ _ _ _ _ hQZ hZQ, hQQ, hZZ]
    have := gram_sum V₀.gram o.iA o.iB o.qA o.qB o.orth' o.orth
    rw [o.iA_qA_add, o.isoA, o.isoB] at this
    rw [← this]
    simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE, hiso, (hfr a a b).2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE, hiso, hsym, (X.zu_orth u b).1]
      simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE', hiso, (hfr a a b).2.2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE', hiso, hsym, (X.zu_orth u b).2]
      simp
  · have h1 := o.rank_add
    have h2 := D.sp.X_rank 0 (Nat.zero_le _)
    have h3 := D.sp.Y_rank 0 (Nat.zero_le _)
    have h4 := D.R.two_le_m
    obtain ⟨c, hc⟩ := D.R.m_even
    simp only [Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero] at h2 h3 ⊢
    omega

end GlobalTheory.Core.SBesEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegrableBoundDoublingIntegrandQuotient
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Dom

theorem exists_integrable_bound_dblIntegrandQ : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q := by
  intro D V μ m hm f₁ f₂ hf₁ hf₂ C' c hC' C N
  have hC'1 : 1 ≤ C' := by
    have h := hC' 1 1
    have e : io V ((1 : GA D V), (1 : GA D V)) = 1 := map_one (io V)
    simp only [e, GlobalTheory.Grow.height_one, mul_one, one_pow] at h
    exact h
  set K : ℝ := max C 0 * (C' * 4 ^ c) ^ N with hK
  have i₁ := _root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D V m hm f₁ hf₁ (c * N)
  have i₂ := _root_.GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D V m hm f₂ hf₂ (c * N)
  refine ⟨fun q => K * ((GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * ‖f₁ q.1.out‖) *
      (GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N) * ‖f₂ q.2.out‖)), (i₁.mul_prod i₂).const_mul K, ?_⟩
  intro E hE hEb q
  obtain ⟨γ₁, hγ₁, h₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, h₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) *
      GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
    rw [hinv]
    refine (hEb _).trans ?_
    have hh := hC' (γ₁ * q.1.out) (γ₂ * q.2.out)
    have hprod : GlobalTheory.Grow.height V (γ₁ * q.1.out) * GlobalTheory.Grow.height V (γ₂ * q.2.out) ≤
        4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
      have := mul_le_mul h₁ h₂ (by linarith) (by linarith)
      linarith
    have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
        C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c := by
      refine hh.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hprod c) (by linarith)
    have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
    calc C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N
        ≤ max C 0 * (C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N) (le_max_right _ _)
      _ = K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
          rw [hK, pow_mul, pow_mul]; ring
  have hμ : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, norm_mul, hμ, mul_one, Complex.norm_conj]
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg (by linarith) (by positivity)) N)
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

end GlobalTheory.Core.Rk.Dom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
section
open Matrix

namespace GlobalTheory.Core.Rk.Exh

theorem exists_orthonormal_of_isLocalRing (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (hτ : ∃ τ : O, τ + s τ = 1)
    (hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u)
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) O) (hQ : Formalism.UG.cT s Q = Q) (hu : IsUnit Q) :
    ∃ a : GL (Fin n) O, Formalism.UG.cT s a.1 * Q * a.1 = 1 := by
  obtain ⟨P, hP, h⟩ := UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or s hs
    (fun x _ => IsLocalRing.isUnit_or_isUnit_one_sub_self x) hτ
    (fun u h1 h2 => (hn u h2 h1).imp fun x hx => by rw [mul_comm, hx])
    (G := Q) (fun a b => congrFun (congrFun hQ b) a) ((Matrix.isUnit_iff_isUnit_det Q).1 hu)
  obtain ⟨R, hR, h'⟩ := UnramifiedHermitian.exists_congr_symm s (G := 1) (H := Q) hP
    (by rw [Matrix.mul_one, h])
  have hR' : IsUnit (R.map s) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hR.map s
  refine ⟨hR'.unit, ?_⟩
  rw [IsUnit.unit_spec, h']
  congr 2
  ext i j
  exact hs _

end GlobalTheory.Core.Rk.Exh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOperators_distinct_real_places_commute_theta : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  first | exact @GlobalTheory.TwoPlaceComm.twoPlace_comm | exact GlobalTheory.TwoPlaceComm.twoPlace_comm | (intros; apply GlobalTheory.TwoPlaceComm.twoPlace_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSignTransposeExchangesLocalGlActionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_sign_transpose_exchanges_local_gl_actions : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b, (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a, (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧ ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  first | exact @GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange | exact GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange | (intros; apply GlobalTheory.Chain.RealIt.SwapFock.locS_locT_exchange <;> assumption)
end

