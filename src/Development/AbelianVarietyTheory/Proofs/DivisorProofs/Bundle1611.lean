module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeSz {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) : ℝ :=
  (cosExp G w : ℝ) * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)

theorem placeSz_nonneg {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) :
    0 ≤ placeSz G w :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C : ℝ)

def DatAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ (w : locPl ch.G A.μ0) x y,
  AbsLe σ ((ch.S.term A.μ0 Φ β w).datum (ch.S.colAt A.μ0 w x) (ch.S.rowAt A.μ0 w y))
    (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def FlipAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ (w : locPl ch.G A.μ0) z,
  AbsLe σ (Tflip ch.W ch.S.B A.μ0 Φ w z) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def CoefAt : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ w : locPl ch.G A.μ0,
  |((ch.S.term A.μ0 Φ β w).coef : ℝ)| ≤ Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

end Claims

section Abs

variable {D : D7}

theorem absLe_mono {σ : D.what₂.LL →+* ℂ} {z : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (hB : B ≤ B') : AbsLe σ z B' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans (Real.exp_le_exp.2 hB)⟩

theorem absLe_mul {σ : D.what₂.LL →+* ℂ} {z z' : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (h' : AbsLe σ z' B') :
    AbsLe σ (z * z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rw [map_mul, norm_mul, Real.exp_add]
  exact mul_le_mul hy hy' (norm_nonneg _) (Real.exp_pos _).le

theorem absLe_prod {ι : Type} (s : Finset ι) {σ : D.what₂.LL →+* ℂ} (z : ι → ℂ) (B : ι → ℝ) (h : ∀ i ∈ s, AbsLe σ (z i) (B i)) :
    AbsLe σ (∏ i ∈ s, z i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact absLe_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absLe_rat (σ : D.what₂.LL →+* ℂ) (q : ℚ) {B : ℝ} (h : |(q : ℝ)| ≤ Real.exp B) : AbsLe σ (q : ℂ) B := by
  refine ⟨(q : D.what₂.LL), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Abs

theorem sum_placeSz_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∑ w : locPl G t, placeSz G w ≤ sig G := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) (placeSz G)]
  have h1 : ∑ w ∈ locPl G t, placeSz G w = ∑ w ∈ G.pl.W0, placeSz G w := by
    refine (Finset.sum_subset (Finset.subset_union_left) fun w _ hw => ?_).symm
    simp [placeSz, (depthAt_of_notMem G hw).1]
  rw [h1, sig]
  unfold Places.W0
  refine (Finset.sum_image_le_of_nonneg fun w _ => placeSz_nonneg G w).trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  rw [placeSz, (depthAt_w G hv).1, G.pl.under_w hv]

end GlobalTheory.ArchTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmetic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem vw_lw_arith : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  intro K _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w a b ha hb
    exact Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb
  · intro w m d hd hmd
    obtain ⟨k, rfl⟩ := hmd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    have hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K) := by
      intro n
      have h := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)
      simpa using h
    refine ⟨hnn m, ?_⟩
    rw [Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
    linarith [hnn k]
  · intro d hd
    have hf := FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    exact hw
  · intro d hd s
    exact Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Plane Chars RealMaps IsMatched IsConst)

variable {D : D7}

def InLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (z : V.V) : Prop := V.frame.equivFun z ∈ Λ

def PlaneSplit (S S₁ : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) : Prop :=
  S.rank = S₁.rank + 2 ∧ Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι ∧ S.hD x x = 0 ∧ S.hD y y = 0 ∧ S.hD x y = 1 ∧
    (∀ u, S.hD (ι u) x = 0 ∧ S.hD (ι u) y = 0) ∧ (∀ u, InLat S₁ Λ₁ u ↔ InLat S Λ (ι u)) ∧
    ∀ z, InLat S Λ z → ∃ (s r : D.host.E) (u : S₁.V), InLat S Λ (s • x) ∧ InLat S Λ (r • y) ∧ InLat S₁ Λ₁ u ∧
      z = s • x + ι u + r • y

def IsStepB {T : Type} {A A' WW B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T A B' WW₁) : Prop :=
  Y.rA = X.rA ∧ (∃ ι x y, PlaneSplit A' B' X.rA'.Λ Y.rA'.Λ ι x y) ∧ ∃ ι x y, PlaneSplit WW WW₁ X.rW.Λ Y.rW.Λ ι x y

def HasConstR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (Γ : Geo σ a a') (R : RealMaps F a a') (χ : Chars F E) (κ : ℂ) : Prop :=
  ∃ om om' Rf, IsMatched B Γ χ om om' R Rf ∧ IsConst B Γ χ om om' R Rf κ

end GlobalTheory.SqStepK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsSelfAnnihilatorSymplecticStandardC
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.RatAnnihF

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ ((1 : AF F) ⊗ₜ[F] e) = (1 : AF F) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem psiV_exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra h
  push_neg at h
  refine GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (DFunLike.ext _ _ fun t => ?_)
  rw [AddChar.one_apply]
  exact h t

theorem adele_rat_of_isGood {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (a : AF F)
    (h : ∀ c : F, B.ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨⟨θ, hθ⟩, -⟩ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ w, θ w (x ⊗ₜ[F] (1 : E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  have hL : ∀ x, L x = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) :=
    fun x => GlobalTheory.StdCharWeilDatum.sum_infFam B θ hθ x
  refine GlobalTheory.RatAnnih.adele_rat (GlobalTheory.StdCharWeilDatum.isCharAF hB.std) (psiV_exists_ne_one hB.std) L
    (continuous_finsetSum _ fun w _ => (hθ w).2) (fun x => ?_) (fun x => ?_) a h
  · rw [hL]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) x) = mixedEmbedding F x := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [e, GlobalTheory.LatVacArith.trace_mixedEmbedding]
    exact Complex.ofReal_ratCast _
  · show B.ψ (pairA F x 0) = _
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA hB.std, hL]
    congr 1
    ring

theorem exists_symplOF_eq (σ : E →ₐ[F] E) (hσ : Function.Surjective σ) {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT)
    {ξ₀ : E} (hξ : ξ₀ ≠ 0) (x : WOF F E nS nT) (i : Fin nT) (j : Fin nS) (e : E) :
    ∃ γ ∈ ratLF F E nS nT, symplOF σ JS JT ξ₀ x γ = Algebra.trace (AF F) (AEF F E) (incAF F E e * x i j) := by
  let g := Function.surjInv hσ
  let P := JS * Matrix.single j i (ξ₀⁻¹ * e) * JT⁻¹
  refine ⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c)), ⟨_, rfl⟩, ?_⟩
  have h := GlobalTheory.RatAnnih.sum_single (incAF F E) JS JT (isUnit_iff_ne_zero.2 hS.2) (isUnit_iff_ne_zero.2 hT.2) j i
    (ξ₀⁻¹ * e) x
  have h2 : hOF σ JS JT x ((incAF F E).toAddMonoidHom.mapMatrix (Matrix.of fun c b => g (P b c))) =
      incAF F E (ξ₀⁻¹ * e) * x i j := by
    rw [← h, hOF]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, g, Function.surjInv_eq hσ]
    rfl
  rw [symplOF, h2, ← mul_assoc, ← RingHom.map_mul, mul_inv_cancel_left₀ hξ]

theorem symplOF_rat (σ : E →ₐ[F] E) [Module.Finite F E] {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (M N : Matrix (Fin nT) (Fin nS) E) :
    ∃ a : F, symplOF σ JS JT ξ₀ ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      algebraMap F (AF F) a := by
  refine ⟨Algebra.trace F E (ξ₀ * ∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a), ?_⟩
  have h : hOF σ JS JT ((incAF F E).toAddMonoidHom.mapMatrix M) ((incAF F E).toAddMonoidHom.mapMatrix N) =
      incAF F E (∑ a, ∑ b, ∑ c, ∑ d, JS⁻¹ a b * σ (N c b) * JT c d * M d a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hOF, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, cAF_incAF, map_sum, map_mul]
  rw [symplOF, h, ← map_mul]
  show Algebra.trace (AF F) (AEF F E) ((1 : AF F) ⊗ₜ[F] _) = _
  rw [GlobalTheory.LatVac.trace_tmul, one_mul]
end

theorem ratLF_annihilator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ x
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  have hσ : Function.Surjective σ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  constructor
  · intro h
    have hent : ∀ i j, ∃ e : E, x i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => adele_rat_of_isGood hB _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplOF_eq σ hσ hS hT hξ x i j (c • e)
        exact (congrArg B.ψ ((GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    refine ⟨Matrix.of M, Matrix.ext fun i j => ?_⟩
    rw [hM i j]
    rfl
  · rintro ⟨M, rfl⟩ _ ⟨N, rfl⟩
    obtain ⟨a, ha⟩ := symplOF_rat σ JS JT ξ₀ M N
    rw [ha]
    exact (GlobalTheory.StdCharWeilDatum.isCharAF hB.std).2.2.1 a

end GlobalTheory.RatAnnihF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
namespace GlobalTheory.SchrCharPure

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  intro F _ _ ψ hψ κ _ a ha b hb f f' hf'
  funext x
  simp only [schr, pureA, add_zero, zero_dotProduct, mul_zero]
  rw [hf']
  by_cases hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a
  · rw [Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu
    have hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2)) := by
      show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      rw [add_zero, zero_add]
      rfl
    have hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i) := by
      have e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i) := by
      have e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hfin : ψ (show AF F from (0, u.2)) = 1 := by
      have := _root_.GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt F ψ hψ κ a ha b hb _ hz
      rw [← hu2] at this
      exact this
    have hAt : At (evI F) (show AF F from (u.1, 0)) := by
      intro w hw
      have h1 : w.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0 := hw
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
      show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
      rw [h1, zero_mul, mul_zero]
    have hinf := hψ.2.2 _ hAt
    have hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i) := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hu1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]
    rw [hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]
    ring
  · rw [Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    simp

end GlobalTheory.SchrCharPure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_mem_schwartzBruhat_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SchrSBFin.schr_mem_SB | exact GlobalTheory.SchrSBFin.schr_mem_SB | (intros; apply GlobalTheory.SchrSBFin.schr_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylSpan

theorem pure_eq_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F (⇑f) (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := by
  rfl

theorem schA_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  intro F _ _ κ _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, g, hg, rfl⟩
    let L : ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
      { toFun := fun g => pureA F (⇑f) g
        map_add' := fun a b => by funext x; simp [pureA, mul_add]
        map_smul' := fun c a => by funext x; simp [pureA]; ring }
    have h := GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg
    have h2 : L g ∈ Submodule.map L (Submodule.span ℂ _) := Submodule.mem_map_of_mem h
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨φ, hφ, hcof, rfl⟩, rfl⟩
    exact ⟨f, φ, hφ, hcof, (pure_eq_pureA f φ).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, hφ, hcof, rfl⟩
    refine Submodule.subset_span ⟨f, _, ?_, pure_eq_pureA f φ⟩
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩

end GlobalTheory.WeylSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiV_ne_one | exact GlobalTheory.PsiNontriv.psiV_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiV_ne_one <;> assumption)
end

