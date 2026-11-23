module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceScale

theorem pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]


set_option maxHeartbeats 4000000 in
theorem exists_scale : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  intro D X X0 Y S YS Z c w j H
  have hch := X.char
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 := ⟨hch.lev, hch.grp, hch.fam, hch.models, hch.chain, hch.thP⟩
  have hio : IoExt X.R.toRealDat := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  obtain ⟨ν', hν', -⟩ := H.rat
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := (Z.scalar (c.twI w) j (c.sd w)).norm ⟨ν', hν'⟩
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨cc, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => X.A3.A.μ0) (X.geo.O j)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin hch.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hO := X.geo.pins j
  obtain ⟨κ, hκ0, hval, hκ⟩ := GlobalTheory.CoefLatConj.exists_coef_scale D _ _ _ X.A3.A X.core X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O
    hC ⟨X.geo.fw⟩ hio j hO cc hc u hu _ hB hBo
  have hfield := hO.2.lift.field
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hcL : ∀ F : VV D.what₂.LL (lamV D j), cc (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (X.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := pow_eq_of_isScale X.R X.geo.v₀ _ hsc hκs
  refine ⟨u, cc, κ, hu, hc, hκ0, hval, hκ, hκs, n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩
  rw [X.phs j, map_one, one_mul] at hνn
  have e : Z.ν (c.twI w) j (c.sd w) ^ (n * k) = κ ^ (n * k) := by
    rw [pow_mul, hνn, ← pow_mul, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
  rw [div_pow, e, div_self (pow_ne_zero _ hκ0)]

end GlobalTheory.PlaceScale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixIntegralIffUniformiserMultipleOnHalf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfUniInt

theorem half_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ IsIntM (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) = 0) := by
  intro D S T βS βT Q e he ϖ hϖ hQ x hx
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  set M := frMapO S T βS βT x with hM
  set a : EAf D := toEAf D (incA D (ϖ : D.host.E)) with ha_def
  have hxm : (x.map fun w => incA D (ϖ : D.host.E) * w) = incA D (ϖ : D.host.E) • x := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hsm : frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w) = a • M := by
    rw [hxm, GlobalTheory.RedHalfDrop.frMapO_smul_eq]
  rw [hsm]
  have hxx : (∑ PP ∈ Q, es PP) • x = x := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hx i j
  have hMe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * M i j = M i j := by
    intro i j
    have h1 := GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT (∑ PP ∈ Q, es PP) x
    rw [hxx] at h1
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  have ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    Subring.subset_closure (Or.inl ⟨⟨(ϖ : D.host.E), ⟨ϖ, rfl⟩⟩, rfl⟩)
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (Subtype.ext h)
  have hsum : (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) = (∑ PP ∈ Q, es PP) * incA D ((ϖ : D.host.E)⁻¹) :=
    (Finset.sum_mul _ _ _).symm
  have hinv : ∀ i j, toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ : D.host.E)⁻¹)) * (a * M i j) = M i j := by
    intro i j
    have hu : toEAf D (incA D ((ϖ : D.host.E)⁻¹)) * a = 1 := by
      rw [ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ hϖ', map_one, map_one]
    rw [hsum, map_mul, mul_assoc, ← mul_assoc (toEAf D (incA D _)), hu, one_mul, hMe]
  have hNe : ∀ i j, toEAf D (∑ PP ∈ Q, es PP) * (a * M i j) = a * M i j := by
    intro i j
    rw [mul_left_comm, hMe]
  have hQ' : ∀ PP ∈ Q, (fun _ => ϖ) PP ∈ PP.asIdeal ∧ (fun _ => ϖ) PP ∉ PP.asIdeal ^ 2 := hQ
  constructor
  · intro hI
    have hN : IsIntM (a • M) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem ha (hI i j)
    refine ⟨hN, fun PP hPP => ?_⟩
    ext i j
    have hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := hN i j; rwa [Matrix.smul_apply, smul_eq_mul] at this
    have key := (_root_.GlobalTheory.IdemKerDiv.integral_div_iff D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).1
      (by rw [hinv]; exact hI i j) PP hPP
    unfold redM
    rw [dite_eq_left (hN i j), Matrix.zero_apply]
    convert key using 3
  · rintro ⟨hN, hR⟩ i j
    have hN' : a * M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := hN i j; rwa [Matrix.smul_apply, smul_eq_mul] at this
    have key := (_root_.GlobalTheory.IdemKerDiv.integral_div_iff D Q es (fun _ => ϖ) hes hc hQ' (a * M i j) hN' (hNe i j)).2
      (fun PP hPP => by
        have h3 := congrFun (congrFun (hR PP hPP) i) j
        unfold redM at h3
        rw [dite_eq_left (hN i j), Matrix.zero_apply] at h3
        convert h3 using 3)
    have e1 := hinv i j
    rw [e1] at key
    exact key

end GlobalTheory.HalfUniInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LiftInfRef

open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def w0 (n : ℕ) : GL (Fin n) ℂ :=
  ⟨(Fin.revPerm.toPEquiv).toMatrix, (Fin.revPerm.toPEquiv).toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem longestWeylElementGL_mul_self (n : ℕ) : w0 n * w0 n = 1 := by
  ext i j
  simp only [w0, Units.val_mul, Units.val_one]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  simp [PEquiv.toMatrix_apply, Matrix.one_apply]

theorem longestWeylElementGL_conj_apply_rev (X : GL (Fin n) ℂ) (i j : Fin n) :
    (w0 n * X * w0 n).val i j = X.val (Fin.rev i) (Fin.rev j) := by
  simp only [w0, Units.val_mul]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

def tinv (B : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨(B⁻¹ : GL (Fin n) ℂ).valᵀ, B.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

omit [NumberField L] [IsCMField L] in
theorem conj_conj (τ : L →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem conj_ne (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by
  intro h
  have h1 : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 h
  have h2 := IsTotallyComplex.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h2
  exact h2 h1

theorem evPt_eq_tinv (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    evPt τ B = evPt (ComplexEmbedding.conjugate τ) (tinv B) := by
  have hne := conj_ne τ
  funext p
  rcases p with ⟨σ, i, j⟩
  by_cases h1 : σ = τ
  · subst h1
    simp [NG.evPt, tinv, Ne.symm hne]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [NG.evPt, tinv, hne]
    · have h3 : σ ≠ ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) := by rwa [conj_conj]
      simp [NG.evPt, h1, h2, h3]

theorem inv_upper {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) : (B⁻¹).val.BlockTriangular id := by
  haveI : Invertible B.val := B.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB

theorem inv_diag {B : GL (Fin n) ℂ} (hB : B.val.BlockTriangular id) (k : Fin n) :
    (B⁻¹).val k k = (B.val k k)⁻¹ := by
  have hI := inv_upper hB
  have e : ((B⁻¹).val * B.val) k k = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hI h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem hwAt_of_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam' : Fin n → ℤ}
    (h : a.HWAt (ComplexEmbedding.conjugate τ) lam') : a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  obtain ⟨ι, hι1, hι2, b, P, hP, v, hv0, hv⟩ := h
  have hR := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP (ComplexEmbedding.conjugate τ)
  refine ⟨ι, hι1, hι2, b, P, hP, evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v, ?_, fun B hB => ?_⟩
  · intro h0
    apply hv0
    have := congrArg (fun x => evM P (evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ x) h0
    simp only [mulVec_mulVec, mulVec_zero] at this
    rwa [← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec] at this
  · set C : GL (Fin n) ℂ := w0 n * tinv B * w0 n with hCdef
    have hBC : tinv B = w0 n * C * w0 n := by
      rw [hCdef, ← mul_assoc, ← mul_assoc, longestWeylElementGL_mul_self, one_mul, mul_assoc, longestWeylElementGL_mul_self, mul_one]
    have hCa : ∀ i j, C.val i j = (B⁻¹).val (Fin.rev j) (Fin.rev i) := by
      intro i j; rw [hCdef, longestWeylElementGL_conj_apply_rev]; rfl
    have hC : C.val.BlockTriangular id := by
      intro i j hij
      rw [hCa]
      exact inv_upper hB (show Fin.rev i < Fin.rev j from Fin.rev_lt_rev.2 hij)
    have hCd : ∀ i, C.val i i = (B.val (Fin.rev i) (Fin.rev i))⁻¹ := fun i => by rw [hCa, inv_diag hB]
    have e1 : (Matrix.of fun i j => MvPolynomial.eval (evPt τ B) (P i j)) =
        evM P (evPt (ComplexEmbedding.conjugate τ) (tinv B)) := by
      rw [evPt_eq_tinv τ B]; rfl
    have hww : evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ
        (evM P (NG.evPt (ComplexEmbedding.conjugate τ) (w0 n)) *ᵥ v) = v := by
      rw [mulVec_mulVec, ← hR.mul, longestWeylElementGL_mul_self, hR.one, one_mulVec]
    have hvC : evM P (NG.evPt (ComplexEmbedding.conjugate τ) C) *ᵥ v = (∏ i, (C.val i i) ^ (lam' i)) • v := hv C hC
    rw [e1, hBC, hR.mul, hR.mul, ← mulVec_mulVec, ← mulVec_mulVec, hww, hvC, mulVec_smul]
    congr 1
    rw [Finset.prod_congr rfl fun i _ => by rw [hCd i, _root_.inv_zpow']]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp [Fin.rev_rev])

end Conj

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open Matrix Formalism.L2.NG GlobalTheory.AlgWtHW NumberField

section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem infOf_conj {a : AlgWt L n} {τ : L →+* ℂ} {lam lam' : Fin n → ℤ} (h : a.HWAt τ lam)
    (h' : a.HWAt (ComplexEmbedding.conjugate τ) lam') : infOf lam' = (infOf lam).map Neg.neg := by
  have e := (_root_.GlobalTheory.AlgWtHW.hw_exists_unique_antitone L n a τ).1.unique h (hwAt_of_conj h')
  have hl : lam' = fun i => -lam (Fin.rev i) := by funext i; rw [e]; simp
  subst hl
  unfold infOf
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

end Conj2

theorem sum_singletons {α : Type} (l : List α) (f : α → ℂ) : (l.map fun k => ({f k} : Multiset ℂ)).sum = ((l.map f : List ℂ) : Multiset ℂ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Multiset.singleton_add]

theorem bindCast (t : ℕ) : ((List.range t >>= fun a => pure (a : ℂ)) : List ℂ) = (List.range t).map (fun a : ℕ => (a : ℂ)) := by
  simp [List.map_eq_flatMap]

theorem range_rev (t : ℕ) (f : ℕ → ℂ) : (Multiset.range t).map (fun c => f (t - 1 - c)) = (Multiset.range t).map f := by
  have h := congrArg (fun l : List ℕ => ((l.map f : List ℂ) : Multiset ℂ)) (List.reverse_range' (s := 0) (n := t))
  simp only [List.map_reverse, Multiset.coe_reverse, List.map_map] at h
  rw [← List.range_eq_range'] at h
  simpa [Multiset.range, Function.comp_def] using h.symm

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

open GlobalTheory.LiftRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lg_of_forall {K : Ctx} {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ B f T, p B f T) : large₂ K p :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => h B f T⟩

theorem evLgG_of_forall {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : ∀ K B f T, p K B f T) : EvLgG p :=
  evLgG_of_evLg ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0,
    fun _ _ => ⟨0, fun K _ _ _ _ _ => lg_of_forall (h K)⟩⟩⟩⟩⟩

end GlobalTheory.LiftInfRef

namespace GlobalTheory.LiftInfRef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.LiftInfRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceUnit

theorem card_residueField_ne_zero {E : Type} [Field E] [NumberField E] (P : Pl E) : Nat.card (kP P) ≠ 0 := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  exact Nat.card_pos.ne'

theorem card_residueField_mem {E : Type} [Field E] [NumberField E] (P : Pl E) : ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  letI : Fintype (kP P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] (P : Pl E) {q l : ℕ} (h : Nat.Coprime q l)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hl
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)

theorem not_mem_of_pD {D : D7} (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hP
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  refine not_mem_of_coprime P ?_ h
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)

theorem isUnit_card_residueField_Oe {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) {P : Pl D.host.E}
    (hl : ((D.ntw.l (c.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : IsUnit ((Nat.card (kP P) : ℕ) : c.Oe w) := by
  haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)
  have h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w)) :=
    GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl)
      (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))
  simpa using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))

theorem tupPrime_isUnit : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι
  have hQ := (H.tup ι hι).2
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_residueField_ne_zero P
  · obtain ⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_residueField_mem P)
  · rw [GlobalTheory.TwistField.tupPrime, Nat.cast_prod]
    refine IsUnit.prod_iff.2 fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine isUnit_card_residueField_Oe c w ?_
    rw [hQ, Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Z.good.delta] at hP
      exact not_mem_of_pD _ (mem_half.1 hP).1
    · exact fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)

end GlobalTheory.PlaceUnit
end

