module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0020
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
public import Formalism.LocalToGlobal.Columns.StandardDeltaIntegralCoeffs
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.BrpColLatOneSpan
section
open NumberField IsDedekindDomain Module
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HN Formalism.HermitianLatticesTheory

section Loc

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem localization_map₃ (p : Ideal (𝓞 K)) [p.IsPrime] (f : V →ₗ[K] V') (A : Submodule (𝓞 K) V) :
    localization₂ p (A.map (f.restrictScalars (𝓞 K))) = (localization₂ p A).map (f.restrictScalars (𝓞 K)) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by exact_mod_cast h0
      rw [this]; exact p.zero_mem
    refine ⟨((s : K)⁻¹) • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul]
      rw [show (algebraMap (𝓞 K) K s) * (s : K)⁻¹ = 1 from mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · simp only [LinearMap.restrictScalars_apply, map_smul]
      simp only [LinearMap.restrictScalars_apply] at hax
      rw [hax, ← algebraMap_smul K s x, smul_smul]
      rw [show (s : K)⁻¹ * (algebraMap (𝓞 K) K s) = 1 from inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    simp only [LinearMap.restrictScalars_apply]
    rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]

end Loc

section LocDel

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

def brpRhoEquiv (lam : DomWeight n) (B : GL (Fin n) K) : VV K (oneW lam) ≃ₗ[K] VV K (oneW lam) :=
  LinearEquiv.ofLinear (Formalism.L2.DIV.rhoK (oneW lam) (fun _ => B)) (Formalism.L2.DIV.rhoK (oneW lam) (fun _ => B⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B) * fun _ => B⁻¹) = 1 := by funext; simp
      rw [this, map_one]; rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : ((fun _ : Unit => B⁻¹) * fun _ => B) = 1 := by funext; simp
      rw [this, map_one]; rfl)

def brpMatEquiv (B : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (B : Matrix (Fin n) (Fin n) K)) (Matrix.mulVecLin ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (by rw [← Matrix.mulVecLin_mul]; simp)
    (by rw [← Matrix.mulVecLin_mul]; simp)

theorem brp_lidx_colLat (M : Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin n) K)
    (hB : IsBasisAt w M B) :
    lidx w.asIdeal (colLat (1 : GL (Fin n) K)) M = vAdd w (B : Matrix (Fin n) (Fin n) K).det := by
  have hfull : Submodule.IsFullLattice K (colLat (1 : GL (Fin n) K)) := by
    refine { toIsLattice := brz_colLat_one_lattice K, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    change (Pi.single i 1 : Fin n → K) ∈ colLat (1 : GL (Fin n) K)
    rw [lc_mem_colLat_one]
    simpa [stdLat, Submodule.mem_pi] using (single_mem_stdLat (E := K) (n := n) i 1)
  rw [bridge_lidx_det_holds K (Fin n → K) w (colLat 1) M (brpMatEquiv K B) hfull ?_]
  · show vAdd w (LinearMap.det (Matrix.toLin' (B : Matrix (Fin n) (Fin n) K))) = _
    rw [LinearMap.det_toLin']
  · rw [hB, lc_colLat_eq_gLat B]
    rfl

end LocDel

section Sum

end Sum

section Weyl

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]

theorem brp_span_lattice {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {j : ℕ}
    (e : Fin j → V) (hsp : Submodule.span K (Set.range e) = ⊤) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) (Set.range e)) := by
  exact Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range e))
theorem brp_colLat_one_span (n : ℕ) :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → K)) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem brp_lcvInf_std (n : ℕ) :
    Formalism.LFunctionChainParameters.LLcv.lcvInf (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 0 := by
  unfold Formalism.LFunctionChainParameters.LLcv.lcvInf
  have : ∀ v, gramPl (Pi.basisFun K (Fin n)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v
      (fun i : Fin n => (Pi.single i 1 : Fin n → K)) = 1 := by
    intro v
    ext a c
    simp only [gramPl, Matrix.of_apply, majAt, fcoord, vecAt, inv_one, Matrix.one_mulVec, Pi.basisFun_repr]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = c
      · subst h; simp
      · simp [Pi.single_apply, Matrix.one_apply, h, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [this]

end Weyl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
section
open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section FockN

def fockN {σ : Type} (f : MvPolynomial σ ℂ) : ℝ := ∑ m ∈ f.support, ‖AddMonoidAlgebra.coeff f m‖ ^ 2 * (mfact m : ℝ)

theorem fockF_self {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = (fockN f : ℂ) := by
  unfold Formalism.REAL.fockF fockN
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, RCLike.mul_conj]
  simp [Formalism.L2.DIV.mfact]

theorem fockN_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockN f :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem fockN_pos {σ : Type} (f : MvPolynomial σ ℂ) (hf : f ≠ 0) : 0 < fockN f := by
  have hne : f.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h0 => hf (MvPolynomial.support_eq_empty.mp h0)
  obtain ⟨m, hm⟩ := hne
  unfold fockN
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨m, hm, ?_⟩
  have h1 : AddMonoidAlgebra.coeff f m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : (0 : ℝ) < (mfact m : ℝ) := by
    have : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
    exact_mod_cast this
  exact mul_pos (pow_pos (norm_pos_iff.mpr h1) 2) h2

theorem fockN_sum_le {σ : Type} (f : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) :
    ∑ m ∈ S, ‖AddMonoidAlgebra.coeff f m‖ ^ 2 * (mfact m : ℝ) ≤ fockN f := by
  classical
  unfold fockN
  rw [← Finset.sum_filter_of_ne (p := fun m => m ∈ f.support)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.mp hm).2)
      (fun _ _ _ => by positivity)
  · intro m _ hne
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hne
    simp [h0]

variable {ι : Type} [Fintype ι] {n : ℕ}

def extremalFockNormProduct (lam : ι → DomWeight n) : ℝ := ∏ τ, fockN (extremal ℂ n (lam τ))

theorem extR_pos (lam : ι → DomWeight n) : 0 < extremalFockNormProduct lam :=
  Finset.prod_pos fun _ _ => fockN_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)

theorem nfL_self (lam : ι → DomWeight n) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfL lam P P = ((fockN P / extremalFockNormProduct lam : ℝ) : ℂ) := by
  rw [nfL_apply, nfAll, fockF_self]
  simp only [fockF_self, extremalFockNormProduct]
  push_cast
  rfl

end FockN

section FinalTheorems

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end FinalTheorems

section Tgt

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def monW (m : MonI lam) : ℝ := (mfact m.1 : ℝ) / extremalFockNormProduct lam

theorem mfact_pos {σ : Type} (m : σ →₀ ℕ) : 0 < mfact m := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem monW_pos (m : MonI lam) : 0 < monW lam m := by
  unfold monW
  exact div_pos (Nat.cast_pos.mpr (mfact_pos _)) (extR_pos lam)

def monD : Matrix (MonI lam) (MonI lam) ℂ := Matrix.diagonal fun m => ((Real.sqrt (monW lam m) : ℝ) : ℂ)

theorem monD_det : IsUnit (monD lam).det := by
  rw [monD, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.2 fun m _ => ?_
  exact_mod_cast (Real.sqrt_pos.2 (monW_pos lam m)).ne'

theorem monH_fcoord (v : InfinitePlace K) (x : MonI lam → K) (m : MonI lam) :
    fcoord (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x m = ((Real.sqrt (monW lam m) : ℝ) : ℂ) * v.embedding (x m) := by
  rw [fcoord, Matrix.nonsing_inv_nonsing_inv _ (monD_det lam)]
  simp [monD, Matrix.mulVec_diagonal, vecAt]

theorem monH_norm (v : InfinitePlace K) (x : MonI lam → K) :
    normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x ^ 2 = ∑ m, monW lam m * ‖v.embedding (x m)‖ ^ 2 := by
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [monH_fcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (monW_pos lam m).le]

end Tgt

section Norm

def hsN {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖U a b‖ ^ 2

theorem hsN_nonneg {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

def FockSubNorm : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (U : ι → Matrix (Fin n) (Fin n) ℂ) (d : ι → ℕ) (F : MvPolynomial (ι × Fin n × Fin n) ℂ),
    (∀ m, AddMonoidAlgebra.coeff F m ≠ 0 → ∀ τ, ∑ a, ∑ s, m (τ, a, s) = d τ) →
    fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U F) ≤ (∏ τ, hsN (U τ) ^ d τ) * fockN F

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def dW (lam : DomWeight n) : ℕ := ∑ s, lam.natW s

def gN (g : ι → GL (Fin n) K) (v : InfinitePlace K) (τ : ι) : ℝ :=
  hsN (((g τ : Matrix (Fin n) (Fin n) K)ᵀ).map v.embedding)

variable [_root_.NumberField.IsTotallyComplex K]

end Norm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCls
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure StepCrd {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  J : Matrix (Fin n) (Fin n) X.E
  f : ℕ
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  emb : X.Tau → X.E →+* ℂ
  lat : cls → Submodule (𝓞 X.E) (Fin n → X.E)
  l0 : Submodule (𝓞 X.E) (Fin n → X.E)
  hJ : J = 1
  hf : f = X.f
  hbad : bad = plUnder X.F Pr.vGs
  hemb : emb = X.embC σ₀
  hlat : lat = L
  hl0 : l0 = stdLat X.E n

def StepCrd.std {X : Fields} (Pr : Primes X) (σ₀ : X.K →+* ℂ) (n : ℕ) {cls : Type}
    (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) : StepCrd Pr σ₀ n L :=
  ⟨1, X.f, plUnder X.F Pr.vGs, X.embC σ₀, L, stdLat X.E n, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure ClsG {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E σ J T f bad
  y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Formalism.L2.Forms.Cls lev))
  y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb
  stabI : ∀ c, stab c →* UJ (σ : E →+* E) J
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (y c).1).toMonoidHom

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def tieLev : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (fun w => (Λ w).H) (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (Ideal.absNorm_eq_natCard P.asIdeal).symm.trans (hPr.vT_norm u P hP)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

def clsG₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  y := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y
  y_bij := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_bij
  y_lat := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).y_lat
  stabI := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI
  stabI_inj := (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs).stabI_range c γ.1 γ.2

def clsG (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    ClsG hc.sig Q.J (Pr.T u) Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsG₁ hc hX hPr σ₀ u Λ c₀ s hS hs

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem badG_eq : CF.badG (d.colRec a) = plUnder d.X.F d.Pr.vGs := by
  exact Set.ext fun v => (plUnder_vGs d.sp.cm d.hPr v).symm

private theorem selfDual_map_crd_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) :
    (d.sp.X i).L0.map ((d.crd i hi).toLinearMap.restrictScalars (𝓞 d.host.E)) = stdLat d.X.E (d.R.N i) := by
  rw [hS.selfDual_span_frame_X i hi, Submodule.map_span, ← Set.range_comp, stdLat_eq_span]
  have hfr : ∀ b, (d.crd i hi) ((d.sp.X i).frame b) = Pi.single (finCongr (d.sp.X_rank i hi) b) (1 : d.host.E) := by
    intro b
    funext j
    show (d.sp.X i).frame.equivFun ((d.sp.X i).frame b) ((finCongr (d.sp.X_rank i hi)).symm j) = _
    rw [Basis.equivFun_self, Pi.single_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩
  change Submodule.span _ (Set.range fun b => (d.crd i hi) ((d.sp.X i).frame b)) = _
  simp_rw [hfr]
  exact congrArg (Submodule.span (𝓞 d.host.E))
    ((finCongr (d.sp.X_rank i hi)).surjective.range_comp (fun j => Pi.single j (1 : d.host.E)))

theorem selfDualLatticeCoords_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.selfDualLatticeCoords (d.colRec a) i hi = stdLat d.X.E (d.R.N i) :=
  selfDual_map_crd_eq_std hS i hi

def stepCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    StepCrd d.Pr d.σ₀ (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  J := CF.gramN (d.colRec a) i hi
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := CF.clsCrd (d.colRec a) u i hi
  l0 := CF.selfDualLatticeCoords (d.colRec a) i hi
  hJ := gramN_eq a hS i hi
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := funext fun c => clsCrd_eq a u i hi c
  hl0 := selfDualLatticeCoords_eq_std a hS i hi

def PtSurj (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), DecoPtSurj d.sp.cm (d.R.N i) (d.Pr.vT u) d.Pr.vGs

def stepClsG (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  clsG d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi)

def classAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.ClsTied (D := d.colRec a) u i hi where
  lev := (stepClsG a hS hH hP u i hi).lev
  y := (stepClsG a hS hH hP u i hi).y
  y_bij := (stepClsG a hS hH hP u i hi).y_bij
  y_lat := (stepClsG a hS hH hP u i hi).y_lat
  stabI := (stepClsG a hS hH hP u i hi).stabI
  stabI_inj := (stepClsG a hS hH hP u i hi).stabI_inj
  stabI_range := (stepClsG a hS hH hP u i hi).stabI_range

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlSplit
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)


include hc in
theorem gls_trace_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a + cO E a := by
  obtain ⟨b0, hb0⟩ := rll_norm_mem hc a
  obtain ⟨b1, hb1⟩ := rll_norm_mem hc (a + 1)
  refine ⟨b1 - b0 - 1, ?_⟩
  rw [map_sub, map_sub, map_one, hb1, hb0, map_add (cO E), map_one]
  ring

end Tr

section Ex

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)


end Ex

end Formalism.L2.Col
end
end

