module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right atPlace_mul_right evFin_atPlace)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace [FiniteDimensional F E] (v : Pl (F := F)) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    rw [e, trace_tmul', trace_tmul', map_mul, AlgHom.commutes]

theorem trace_split {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = splitProj t y + splitProj (t.comp σ) y := by
  rw [← Algebra.trace_eq_of_algEquiv (splitAlgEquiv h t) y, Algebra.trace_prod_apply, splitAlgEquiv_apply]
  simp [Algebra.trace_self_apply]

theorem piW_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : AE F E) :
    piW (t.comp σ) (cA σ y) = piW t y := by
  have e : compFin F E v (cA σ y) = sigR (Fv F v) σ (compFin F E v y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => rfl
  change splitProj (t.comp σ) (compFin F E v (cA σ y)) = splitProj t (compFin F E v y)
  rw [e]
  exact splitProj_comp_sigR h t _

theorem piW_inclR {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (AF F) x) = t x := by
  change splitProj t (evFin F v 1 ⊗ₜ[F] x) = t x
  rw [map_one]
  exact splitProj_inclR t x

theorem piW_tensAt {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  change splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

theorem at_tensAt {v : Pl (F := F)} (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro a ha
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change evFin F v a ⊗ₜ[F] (1 : E) = 0
    rw [ha, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem eq_liftV_of_at {v : Pl (F := F)} {a : AF F} (ha : At (evFin F v) a) : a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  have h1 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h2 := ha _ h1
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
  calc a = atPlace v 1 * a := h2
    _ = atPlace v (1 * evFin F v a) := atPlace_mul_right v 1 a
    _ = GlobalTheory.LatVac.liftV v (evFin F v a) := by rw [one_mul]; rfl

end GlobalTheory.OppLinChar

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (tensAt)

theorem char_eq_psi_symp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Z
  have h := hB.cm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  refine ⟨Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0)), ?_, ?_, ?_⟩
  · intro a ha
    ext k l
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact at_tensAt _ a ha
  · ext k l
    simp [piW_tensAt]
  · intro x hxv hx
    set u : Matrix (Fin n) (Fin d) (AE F E) := Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0))
      with hu_def
    have hx' : ∀ i j, piW t (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
    have hJX : ∀ i k, piW (t.comp σ) (incM F X.J i k) = t (X.J k i) := fun i k => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hX.herm]
    have hJW : ∀ j l, piW (t.comp σ) (incM F W.J j l) = -t (W.J l j) := fun j l => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hW.skew, map_neg]
    have hu : ∀ k l, piW (t.comp σ) (cA σ (u k l)) = -Z k l := fun k l => by
      rw [piW_cA h, hu_def, Matrix.of_apply, piW_tensAt, splitProj_symm]
    set S := symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u with hS_def
    have hat : At (evFin F v) S := by
      intro a ha
      rw [smul_eq_mul, ← one_mul S, ← mul_assoc, hS_def, ← GlobalTheory.LatVac.symp_smul_smul]
      have h0 : a • x = 0 := hxv a ha
      rw [h0]
      simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
    have hev : evFin F v S = ∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) *
        (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j := by
      rw [hS_def, GlobalTheory.WeilM.symp, evFin_trace, trace_split h t]
      change piW t _ + piW (t.comp σ) _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, hx', hJX, hJW, hu]
      have key : ∀ (f : Fin n → Fin d → Fin n → Fin d → Fv F v),
          ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
        intro f
        calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, Units.val_one, Matrix.transpose_one,
        Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib]
      refine (key _).trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    change B.ψ S = B.ψ (GlobalTheory.LatVac.liftV v _)
    rw [← hev, ← eq_liftV_of_at hat]

end GlobalTheory.OppLinChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundOfAllEstimates
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LowCover

theorem numeric {M E b K C1 muB mu0 : ℝ} (hb : 0 ≤ b) (hbE : b ≤ E) (hbK : b ≤ K) (hMK : |M| ≤ K) (hC1 : 0 ≤ C1)
    (h : (-M - C1 * E - 2 * b) - b / K * (|-M - C1 * E - 2 * b| + 2 * K) ≤ muB) (hR : muB - 2 * b ≤ mu0) :
    -M - (2 * C1 + 9) * E ≤ mu0 := by
  have hK : 0 < K ∨ b = 0 := by
    rcases eq_or_lt_of_le hb with h0 | h0
    · exact Or.inr h0.symm
    · exact Or.inl (h0.trans_le hbK)
  have hE : 0 ≤ E := hb.trans hbE
  have hC1E : 0 ≤ C1 * E := mul_nonneg hC1 hE
  have ht : |-M - C1 * E - 2 * b| ≤ |M| + C1 * E + 2 * b := by
    have := abs_sub (-M - C1 * E) (2 * b)
    have h2 := abs_sub (-M) (C1 * E)
    rw [abs_neg] at h2
    rw [abs_of_nonneg hC1E] at h2
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * b)] at this
    linarith
  rcases hK with hK | hb0
  · set ε := b / K with hε
    have hε0 : 0 ≤ ε := div_nonneg hb hK.le
    have hε1 : ε ≤ 1 := (div_le_one hK).2 hbK
    have hεK : ε * K = b := div_mul_cancel₀ b hK.ne'
    have h1 : ε * |-M - C1 * E - 2 * b| ≤ ε * |M| + ε * (C1 * E + 2 * b) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hε0
    have h2 : ε * |M| ≤ b := hεK ▸ mul_le_mul_of_nonneg_left hMK hε0
    have h3 : ε * (C1 * E + 2 * b) ≤ C1 * E + 2 * b := by
      have : 0 ≤ C1 * E + 2 * b := by linarith
      nlinarith
    have h4 : ε * (|-M - C1 * E - 2 * b| + 2 * K) = ε * |-M - C1 * E - 2 * b| + 2 * b := by
      rw [mul_add, ← hεK]; ring
    rw [h4] at h
    nlinarith
  · subst hb0
    simp only [zero_div, zero_mul, sub_zero, mul_zero] at h hR
    nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rkK_bot' {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] :
    Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
  simp [Formalism.HN.rkK]

theorem lowAt_mono {p : PtAt ex Csz} {i : Fin D.R.m} {C C' : ℝ} (h : LowAt p i C) (hC : C ≤ C') (hE : 0 ≤ unitE p) :
    LowAt p i C' := by
  unfold LowAt at *
  nlinarith [mul_le_mul_of_nonneg_right hC hE]

theorem lowAt_of_cover (p : PtAt ex Csz) (i : Fin D.R.m) (PP CS CF CU : ℝ) (hCF : 0 ≤ CF) (hCU : 0 ≤ CU)
    (hS : SizeAt p i PP CS) (Y : Cov p i) (hG : DeepGoodAt p i Y) (hR : RingAt p i Y) (hM : MapsAt p i Y)
    (hK : RkAt p i Y PP) (hGm : GminAt p i Y PP) (hF : FlatAt p i Y CF) (hU : UAt p i Y CU) :
    LowAt p i (2 * (CF + CU) + 9) := by
  obtain ⟨hb1, hbE, -, -, hMK, hbK, -⟩ := hS
  obtain ⟨hGk, hGm', -, -, hrk0, -, -, -⟩ := hG
  obtain ⟨n, φ, hint, hinj, hnorm, hrk⟩ := hM
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hKpos : 0 < PP * kap p i := by linarith
  have hBle : latDeep p i Y ≤ latW Y.U (Gk p i) := inf_le_left
  have hBfg : (latDeep p i Y).FG := GlobalTheory.HalfRankSub.fg_of_le_fg hGk.2.1 hBle
  have hA0 : latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1)))) ≠ ⊥ := by
    intro h
    change 0 < Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) at hrk0
    rw [h] at hrk0
    rw [rkK_bot'] at hrk0
    exact lt_irrefl _ hrk0
  have hrkR : (n : ℝ) * Formalism.HN.rkK (latDeep p i Y) ≤
      (1 + L.sc.b / (PP * kap p i)) * Formalism.HN.rkK (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := by
    have h1 : ((n * Formalism.HN.rkK (latDeep p i Y) : ℕ) : ℝ) ≤ (Y.rk (Gs p i (cZero D ((i : ℕ) + 1))) : ℝ) := by
      exact_mod_cast hrk
    push_cast at h1
    exact h1.trans hK
  have hmu : Y.mu (Gs p i (-(cZero D ((i : ℕ) + 1)))) =
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) := rfl
  have ht : -mainT p i - (CF + CU) * unitE p - 2 * L.sc.b ≤
      slope_sq (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) -
        2 * L.sc.b := by
    unfold FlatAt at hF
    unfold UAt at hU
    rw [← hmu]
    nlinarith
  have hd := GlobalTheory.DescentFamily.descent Y.d.c₂.F _ _ (Y.nrm (Gs p i (-(cZero D ((i : ℕ) + 1))))) (Y.nrm (Gk p i))
    (latW Y.U (Gs p i (-(cZero D ((i : ℕ) + 1))))) (latDeep p i Y) n φ L.sc.b (PP * kap p i)
    (L.sc.b / (PP * kap p i)) (-mainT p i - (CF + CU) * unitE p - 2 * L.sc.b) hGm'.1 hGk.1 hGm'.2.1 hBfg hA0
    hint hinj hnorm hGm hKpos.le (div_nonneg (by linarith) hKpos.le) hrkR ht
  unfold LowAt
  unfold RingAt at hR
  exact numeric (by linarith) hbE hbK hMK (by linarith) hd hR

end GlobalTheory.CovTop.LowCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def IsTest (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (yb : Sp 𝓞_ℂ_[p] ⟶ X) : Prop :=
  (∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb) ∧
    Set.range (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ⊆ Xw

def GeomIrr {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V) (Xw : X.Opens) : Prop :=
  ∀ (k : Type) [Field k] (f : V →+* k), Function.Injective f → IrreducibleSpace ↑(pullback (Xw.ι ≫ s) (spMap f))


section Minors

variable {R V J : Type} [CommRing R] [CommRing V] {N g m : ℕ}

def pairDet (h U : Fin m → Fin g → R) : R := (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b).det

def covec (β : V →+* R) (T : J → Fin N → V) (h : Fin N → Fin g → R) (I : Fin m → J) : Fin m → Fin g → R :=
  fun k b => ∑ a, β (T (I k) a) * h a b

end Minors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W).toSubring fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff (R := c.V W) (K := c.F).1
      ((map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a)).tower_top)
    exact hy ▸ y.2

section Lie

variable {X : Scheme.{0}} (t : SAB H X) {g m : ℕ}

def IsEigG {S : Type} [CommRing S] (σ : 𝓞 E →+* S) (u : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∀ a, u ≫ (t.act.act a).left = spMap (epsMul (σ a)) ≫ u

def EigRowsAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin m → Fin g → S) : Prop :=
  ∀ k u, IsCombAtG t x e (U k) u → IsEigG t σ u

def EigAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin g → Fin g → S) : Prop :=
  EigRowsAt t x σ e U ∧
    ∀ w v, IsCombAtG t x e w v → IsEigG t σ v → ((discr E : ℤ) : S) • w ∈ Submodule.span S (Set.range U)

def bcV {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    Fin g → (Sp (DualNumber S) ⟶ t.G.left) := fun i => spMap (dualMap φ) ≫ e i

def EigFam {R : Type} [CommRing R] (x : Sp R ⟶ X) (σ : 𝓞 E →+* R) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (U : Fin g → Fin g → R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S), EigAt t (spMap φ ≫ x) (φ.comp σ) (bcV t φ e) fun k b => φ (U k b)

end Lie

abbrev Ind (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult τ) ⊕ Fin (Dw.mult (conjEmb τ))


section Model

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))

def OverIncl (hle : c.F ≤ c'.F) : Prop :=
  r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom

def IsCover (hle : c.F ≤ c'.F) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) (Xw : Y.X.Opens) : Prop :=
  OverIncl r hle ∧ (∀ x : c.F, (x : ℂ) ∈ W ↔ la.valuation c.F x ≤ 1) ∧ (p : ℂ) ∈ W.nonunits ∧
  (p : c'.F) ∈ (c'.V W).nonunits ∧ (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
  (∀ z, Y.j z ∈ Xw → r z ∈ (Z : Set (Xo.XF c))) ∧ GeomIrr Y.s Xw ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
    x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
    Set.range x ⊆ (Z : Set (Xo.XF c)) →
    ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range (yy ≫ Y.j) ⊆ Xw

def GVal (τ : E →+* ℂ) (f : Rul Xo c) {k : Type} [Field k] [Algebra c.F k] (yy : Sp k ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber k) ⟶ Y.t.G.left)) (U₁ : Fin (Dw.mult τ) → Fin g → k)
    (U₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → k) (fv : k) : Prop :=
  ∀ y : FrPt Xo c k, Tested y → GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) k),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₁ i) (w₁ i ≫ Y.m.φ)) → (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₂ i) (w₂ i ≫ Y.m.φ)) →
      (∀ i, IsCombAt y.x (y.u τ) (g₁ i) (w₁ i ≫ ν.φ)) → (∀ i, IsCombAt y.x (y.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ)) →
      fv * g₁.det = g₂.det * evR Xo c f y

variable {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)]


variable (p E) in
abbrev PtP : Type 1 := Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)

def PtOn (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Y.j ∧ IsGrpPullback P.G Y.t.G yb π ∧
    (∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left) ∧ IsGrpPullback P.A.A Y.oF.t.G yy ψ ∧
    ψ ≫ Y.m.φ = P.gen ≫ π ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ)

def ITie (P : PtP E p) {G : Scheme.{0}} (π : P.G.left ⟶ G) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ G) : Prop :=
  ∃ xG : LieG P.G, Corr P x.1 xG.1 ∧ xG.1.left ≫ π = u

def HTApprox (n : ℕ) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) {N g : ℕ} (a : Fin N → Dw.La)
    (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (h : Fin N → Fin g → 𝓞_ℂ_[p]) : Prop :=
  ∀ (m : Fin N) (t : P.T), (t.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left → ∀ (k : Fin g) (x : LieG P.Gt),
    ITie P π x (e k) → h m k - (P.al₀ t).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}

variable [Algebra c.F ℂ_[p]]

def KapSpec (τ : E →+* ℂ) (f : Rul Xo c) (n : ℕ) {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ → Fin N → c'.V W)
    (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (κ : ℂ_[p]) : Prop :=
  ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
  ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
    (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ)) e U₁ →
    EigAt Y.t yb (β.comp (embV c' W (conjEmb τ))) e U₂ → HTApprox Y n yy P π ψ a e h →
    (∃ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) ∧
    ∀ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖ →
      ∀ fv : ℂ_[p], GVal Y r ν τ f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
        (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
        ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
          (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖

end Model

def HTLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ)
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)),
    IsTanBasis Y.t ξ e → ∀ (N : ℕ) (a : Fin N → Dw.La) (𝔭 : Ideal R), 𝔭.IsPrime →
    ∃ (f : R) (h : Fin N → Fin g → Localization.Away f), f ∉ 𝔭 ∧
      ∀ (φ : Localization.Away f →+* 𝓞_ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
        (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y (spMap (φ.comp (algebraMap R _)) ≫ ξ) yy P π ψ →
        HTApprox Y n yy P π ψ a (bcV Y.t (φ.comp (algebraMap R _)) e) fun m k => φ (h m k)

def GenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
      ∃ f : Aˣ, ∀ (k : Type) [Field k] [Algebra c.F k] (φ : A →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap φ ≫ ξ →
        GVal Y r ν τ.1 s.sig yy (bcV Y.t φ e) (fun k b => φ (U₁ k b)) (fun k b => φ (U₂ k b)) (φ f)

section BaseChange

variable {X : Scheme.{0}} {t : SAB H X} {g : ℕ} {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']

theorem bcV_bcV (φ : R →+* S) (ψ : S →+* S') (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    bcV t ψ (bcV t φ e) = bcV t (ψ.comp φ) e := by
  funext i
  rw [bcV, bcV, bcV, ← Category.assoc, spMap_spMap]
  congr 2
  ext s <;> simp [dualMap]

theorem sp_sp (φ : R →+* S) (ψ : S →+* S') (x : Sp R ⟶ X) : spMap ψ ≫ spMap φ ≫ x = spMap (ψ.comp φ) ≫ x := by
  rw [← Category.assoc, spMap_spMap]

theorem isTanBasis_bc {x : Sp R ⟶ X} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x e)
    (φ : R →+* S) : IsTanBasis t (spMap φ ≫ x) (bcV t φ e) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun S' _ ψ w hw => ?_⟩
  · rw [bcV, Category.assoc, (h.1 i).1, sp_sp, sp_sp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · have e1 : (1 : Over.mk (spMap φ ≫ x) ⟶ t.G) = (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [e1, Over.comp_left, ← (h.1 i).2, bcV, ← Category.assoc, spMap_spMap]
    change _ = spMap φ ≫ _ ≫ _
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sp_sp] at hw ⊢
    have := h.2 S' (ψ.comp φ) w hw
    change ∃! a, IsCombAtG t _ (bcV t ψ (bcV t φ e)) a w
    rw [bcV_bcV]
    exact this

theorem bot_map [IsDomain R] [IsDomain S] {φ : R →+* S} (hφ : Function.Injective φ) (x : Sp R ⟶ X) :
    (spMap φ ≫ x) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) = x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg x ?_)
  exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot φ).1 hφ)

end BaseChange

theorem coe_valued (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl), Valuation.embedding_restrict]

end GlobalTheory.FlatModel

end
end

