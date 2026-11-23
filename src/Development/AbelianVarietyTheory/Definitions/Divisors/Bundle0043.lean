module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

abbrev RatPt (G : Geo K) (s : Fin G.D → Fin G.N → K) : Type := PtsOver K ((G.ideal s).subschemeι ≫ G.str)

namespace RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K} (x : RatPt G s)

def pt : G.Pt K := ⟨x.1 ≫ (G.ideal s).subschemeι, (Category.assoc _ _ _).trans x.2⟩

def along {Ω : Type} [Field Ω] (φ : K →+* Ω) : Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ) :=
  ⟨spMap φ ≫ x.1, by rw [Category.assoc, x.2, spMap, spMap, ← Spec.map_comp]; rfl⟩

def gen (k : Fin G.n) : K := ∑ j, G.w j k * G.coords x.pt.1 j

def c₁ (τ : K →+* ℂ) : ℝ := archSize (G.A τ) fun j => τ (G.coords x.pt.1 j)

def c₂ (τ : K →+* ℂ) : ℝ := archSize (G.A₂ τ) fun j => τ (G.second.coords x.pt.1 j)

def ht : ℝ := vecHt x.gen x.c₁

theorem le_chart (j : ℤ) : ⊤ ≤ (x.1 ≫ (G.ideal s).subschemeι) ⁻¹ᵁ (tw G.L₂ G.L j).U
    (twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
  fun _ hw => mem_tw_U.2 ⟨G.second.le_chartAt x.pt.1 hw, G.le_chartAt x.pt.1 hw⟩

def val (j : ℕ) : G.SecOn s j →ₗ[K] K where
  toFun g := valOn x.1 _ (x.le_chart j) g
  map_add' f g := map_add _ f g
  map_smul' c g := valOn_smul x.1 x.2 _ _ c g

theorem c₁_pos (τ : K →+* ℂ) : 0 < x.c₁ τ := archSize_pos (G.herm τ) fun h =>
  G.geom.alg.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem c₂_pos (τ : K →+* ℂ) : 0 < x.c₂ τ := archSize_pos (G.herm₂ τ) fun h =>
  G.alg₂.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem c₂_conj (τ : K →+* ℂ) : x.c₂ ((starRingEnd ℂ).comp τ) = x.c₂ τ := by
  let w (σ : K →+* ℂ) : CxPts G.str σ := Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap σ) (x.along σ)
  have e (σ : K →+* ℂ) : (G.φ₂ σ).φ (G.second.chartAt (ptOf x.pt.1)) (w σ) = Real.log (x.c₂ σ ^ 2) := by
    refine (G.second.weight_φ _ _ σ _ (w σ)).trans (congrArg (fun y => Real.log (archSize _ y ^ 2)) (funext fun k => ?_))
    exact Points.valR_spMap_comp σ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
  have h := G.isConj_φ₂ τ (G.second.chartAt (ptOf x.pt.1)) (w τ) (w _) (by
    change (spMap _ ≫ x.1) ≫ _ = spMap _ ≫ (spMap τ ≫ x.1) ≫ _
    rw [← Category.assoc (spMap (starRingEnd ℂ)), ← Category.assoc (spMap (starRingEnd ℂ)), ← Spec.map_comp]
    rfl) fun _ _ => G.second.le_chartAt x.pt.1 (Set.mem_univ _)
  have p := x.c₂_pos τ
  have p' := x.c₂_pos ((starRingEnd ℂ).comp τ)
  exact (pow_left_inj₀ p'.le p.le two_ne_zero).1
    (Real.log_injOn_pos (pow_pos p' 2) (pow_pos p 2) ((e _).symm.trans (h.trans (e τ))))

theorem exp_neg_weight (j : ℕ) (τ : K →+* ℂ) :
    Real.exp (-(Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ)) = ((x.c₂ τ * x.c₁ τ ^ j) ^ 2)⁻¹ := by
  have e : (Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ) = Real.log (x.c₂ τ ^ 2) + j * Real.log (x.c₁ τ ^ 2) := by
    simp only [Geo.weightOn, Weight.pull, Weight.linComb, Geo.φTw, Weight.tens, Weight.zpow, Geo.φ, Geo.φ₂,
      HermSys.weight_φ]
    have a₁ : ∀ k, secVal G.str τ (G.b k) (G.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.le_chartAt x.pt.1) _
    have a₂ : ∀ k, secVal G.str τ (G.b₂ k) (G.second.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.second.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
    simp only [id, a₁, a₂, Finset.univ_unique, Finset.sum_singleton, Int.cast_one, one_mul, Int.cast_natCast, c₁, c₂]
  have p₁ := x.c₁_pos τ
  have p₂ := x.c₂_pos τ
  rw [e, Real.exp_neg, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity), mul_pow,
    ← pow_mul, ← pow_mul, mul_comm 2 j]

theorem nsq_eq (j : ℕ) (τ : K →+* ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) (g : ι → G.SecOn s j) :
    (Geo.weightOn s j τ).nsq (∑ i, c i • cval τ (g i)) (x.along τ) =
      ‖∑ i, c i * τ (x.val j (g i))‖ ^ 2 / (x.c₂ τ * x.c₁ τ ^ j) ^ 2 := by
  have hw : x.along τ ∈ ptsIn ((G.ideal s).subschemeι ≫ G.str) τ (((tw G.L₂ G.L j).pull (G.ideal s).subschemeι).U
      fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
    fun _ _ => mem_pull.2 (x.le_chart j (Set.mem_univ _))
  rw [Weight.nsq_eq _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (cval_mem τ (g i))) hw, exp_neg_weight,
    div_eq_mul_inv]
  refine congrArg (fun r => ‖r‖ ^ 2 * _) ?_
  refine ((congrFun (Finset.sum_apply _ _ _) _).trans (Finset.sum_apply _ _ _)).trans ?_
  exact Finset.sum_congr rfl fun i _ => congrArg (c i * ·)
    ((cval_eq_val τ _ _ _ mem_ptsIn_top hw).trans (evalPt_spMap_comp τ x.1 _ _ _ _))

theorem val_mulSecOn (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j) :
    x.val (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) =
      (∑ k, u k * G.coords x.pt.1 k) * x.val j g := by
  refine (valOn_mulSecOn G.isLB₂ G.isLB (G.comb u) _ g x.1 _ _ (G.le_chartAt x.pt.1) (x.le_chart j)
    (x.le_chart _)).trans (congrArg (· * _) ?_)
  refine (Points.valR_eq _ _ (G.le_chartAt x.pt.1) _).symm.trans ((G.val_comb x.pt.1 u).trans ?_)
  rw [LinSys.baseHom_ptOver]
  rfl

theorem along_injective (hs : G.IsGood s) {Ω : Type} [Field Ω] (φ : K →+* Ω) :
    Function.Injective fun x : RatPt G s => x.along φ := fun x x' h => by
  have := hs.finite
  have : IsAffine (G.ideal s).subscheme := isAffine_of_isAffineHom ((G.ideal s).subschemeι ≫ G.str)
  have e : spMap φ ≫ x.1 = spMap φ ≫ x'.1 := congrArg Subtype.val h
  refine Subtype.ext (ext_evalPt (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => φ.injective ?_))
  rw [← evalPt_spMap_comp φ x.1 ⊤ le_top le_top, ← evalPt_spMap_comp φ x'.1 ⊤ le_top le_top]
  simp only [e]

end RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K}

def Coord.AtPoints {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (x : Fin δ ≃ RatPt G s) : Prop :=
  ∀ p, (∀ j g, Co.ev j g p = (x p).val j g) ∧ Co.y p = G.coords (x p).pt.1 ∧ ∀ τ, Co.c₂ τ p = (x p).c₂ τ

theorem RatPt.along_bijective (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (φ : K →+* Ω) : Function.Bijective fun x : RatPt G s => x.along φ := by
  have := hs.finite
  have := hs.etale
  letI := φ.toAlgebra
  have hB := isLB_tw G.isLB₂ G.isLB 0
  have : Finite (Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ)) := finite_ptsOver _ Ω
  refine (RatPt.along_injective hs φ).bijective_of_nat_card_le (le_of_eq ?_)
  exact (finrank_H0On (p := G.str) (I := G.ideal s) hB Ω).symm.trans
    ((finrank_H0On hB (AlgebraicClosure K)).trans (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, h⟩).symm)

theorem exists_coord_atPoints (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {δ : ℕ} (x : Fin δ ≃ RatPt G s) : ∃ Co : Coord G hs δ, Co.AtPoints x := by
  have := hs.finite
  have := hs.etale
  let φ (j : ℕ) : G.SecOn s j →ₗ[K] (Fin δ → K) := LinearMap.pi fun p => (x p).val j
  have bij (j : ℕ) : Function.Bijective (φ j) := by
    have hB := isLB_tw G.isLB₂ G.isLB (j : ℤ)
    choose r hr using h
    have inj : Function.Injective (φ j) := (injective_iff_map_eq_zero _).2 fun g hg => by
      have hr' (w : PtsOver (AlgebraicClosure K) ((G.ideal s).subschemeι ≫ G.str)) :
          w.1 = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 := (congrArg Subtype.val (hr w)).symm
      refine eq_zero_of_forall_valOn_eq_zero (Ω := AlgebraicClosure K) hB
        (fun w => twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1)))
        (fun w => by rw [hr' w]; exact fun _ _ => (r w).le_chart j (Set.mem_univ _)) fun w => ?_
      have e : (r w).val j g = 0 := by simpa [φ] using congrFun hg (x.symm (r w))
      have key : ∀ (z : Sp (AlgebraicClosure K) ⟶ (G.ideal s).subscheme) (hz),
          z = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 →
          valOn z (twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1))) hz g = 0 := by
        rintro _ hz rfl
        exact (evalPt_spMap_comp _ (r w).1 _ _ _ _).trans ((congrArg _ e).trans (map_zero _))
      exact key _ _ (hr' w)
    have := finite_H0On (p := G.str) (I := G.ideal s) hB
    refine ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 inj⟩
    rw [finrank_H0On hB (AlgebraicClosure K), Module.finrank_fin_fun, ← Nat.card_fin δ, Nat.card_congr x]
    exact (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, fun w => ⟨r w, hr w⟩⟩).symm
  refine ⟨⟨fun j => LinearEquiv.ofBijective (φ j) (bij j), fun p => G.coords (x p).pt.1, fun σ p => (x p).c₂ σ,
    fun _ => G.geom.alg.bpf.coords_ne_zero _, fun σ p => (x p).c₂_pos σ, fun σ p => (x p).c₂_conj σ,
    fun j u g => funext fun p => (x p).val_mulSecOn j u g, fun j σ m c g => ?_⟩, fun p => ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩⟩
  refine (csq_pointHerm _ _ _ σ c g).trans ?_
  rw [← finsum_comp_equiv (x.trans (Equiv.ofBijective _ (RatPt.along_bijective hs h σ))), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).nsq_eq j σ c g

section Split

variable {F : Type} [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]
  (s : Fin G.D → Fin G.N → E)

def RatPt.geomPt (x : RatPt (G.baseChange E) s) : (G.toLinSys.baseChange E).Pt (AlgebraicClosure E) :=
  Points.PtsOver.map ((G.baseChange E).ideal s).subschemeι rfl _ (x.along (algebraMap E (AlgebraicClosure E)))

variable {G E s}

theorem RatPt.ptHeight_geomPt (x : RatPt (G.baseChange E) s) :
    haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
    G.ptHeight (LinSys.toBase (RatPt.geomPt G E s x)) = x.ht := by
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
  obtain ⟨c, hc, e⟩ := G.exists_coords_baseChange E x.pt.1
  have h₀ := G.geom.alg.bpf.coords_ne_zero (x.pt.1 ≫ G.bcFst E)
  have h₁ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm (AlgebraicClosure E) _ 1 h₀ one_ne_zero
  have h₃ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ c h₀ hc
  have h₄ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ 1 (smul_ne_zero hc h₀) one_ne_zero
  rw [one_smul] at h₁ h₄
  have h₅ : G.coords (LinSys.toBase (RatPt.geomPt G E s x)).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords (x.pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  rw [HermSys.ptHeight, h₅, h₁]
  exact (h₃.symm.trans h₄).trans (congrArg (pointHeight G.w G.A) e.symm)

theorem Split.along_surjective (h : Split G.toTuple E s) :
    Function.Surjective fun x : RatPt (G.baseChange E) s => x.along (algebraMap E (AlgebraicClosure E)) := fun w => by
  obtain ⟨x₀, e⟩ := h w.1 w.2
  refine ⟨⟨x₀, ?_⟩, Subtype.ext e.symm⟩
  have h₁ := (G.baseChange E).comp_str (x₀ ≫ ((G.baseChange E).ideal s).subschemeι)
  have h₃ := (Category.assoc _ _ _).symm.trans h₁
  have h₂ := (Spec.map_comp _ _).trans ((congrArg (spMap (algebraMap E (AlgebraicClosure E)) ≫ ·) h₃).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).symm.trans w.2)))
  refine h₃.trans (congrArg spMap (RingHom.ext fun a => (algebraMap E (AlgebraicClosure E)).injective ?_))
  exact congrArg (fun f => f.hom a) (Spec.map_injective h₂)

theorem Split.geomPts_eq (h : Split G.toTuple E s) :
    G.geomPts E (G.linSection E s) = Set.range (RatPt.geomPt G E s) := by
  refine Set.ext fun y => ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨_, congrArg Subtype.val hx⟩⟩
  obtain ⟨x, hx⟩ := h.along_surjective ⟨z, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hz).trans y.2)⟩
  exact ⟨x, Subtype.ext ((congrArg (fun t => t.1 ≫ _) hx).trans hz)⟩

theorem RatPt.geomPt_injective (hs : (G.baseChange E).IsGood s) : Function.Injective (RatPt.geomPt G E s) :=
  fun _ _ h => RatPt.along_injective hs _ (Subtype.ext ((cancel_mono ((G.baseChange E).ideal s).subschemeι).1
    (congrArg Subtype.val h)))

theorem Split.exists_coord (h : Split G.toTuple E s) (hs : (G.baseChange E).IsGood s) :
    ∃ (x : Fin (G.geomPts E (G.linSection E s)).ncard ≃ RatPt (G.baseChange E) s)
      (Co : Coord (G.baseChange E) hs (G.geomPts E (G.linSection E s)).ncard),
      Co.AtPoints x ∧ G.cycleHeight E (G.linSection E s) = ∑ p, (x p).ht := by
  have hfin := (Geo.isGood_baseChange_iff.1 hs).finite_geomPts
  have : Finite (RatPt (G.baseChange E) s) :=
    (Set.finite_range_iff (RatPt.geomPt_injective hs)).1 (h.geomPts_eq ▸ hfin)
  have e : Nat.card (RatPt (G.baseChange E) s) = (G.geomPts E (G.linSection E s)).ncard := by
    rw [h.geomPts_eq, Set.ncard_range_of_injective (RatPt.geomPt_injective hs)]
  let x := (Finite.equivFinOfCardEq e).symm
  obtain ⟨Co, hCo⟩ := exists_coord_atPoints hs h.along_surjective x
  refine ⟨x, Co, hCo, ?_⟩
  rw [HermSys.cycleHeight]
  refine (finsum_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
  rw [finsum_mem_range (RatPt.geomPt_injective hs), ← finsum_comp_equiv x, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).ptHeight_geomPt

end Split

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice

namespace GlobalTheory.HSShort

def ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (G : MvPolynomial (Fin B × Fin N) F) : ℝ := formHeight 0 w A G

def cst (n Λ : ℝ) : ℝ := Real.log (n * Λ) + (Real.log n + 1) / 2

structure Lat {F : Type} [Field F] [NumberField F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ) : Prop where
  pos : 0 < N
  spans : Submodule.span F (Set.range w.col) = ⊤
  det : ∀ σ, (A σ).det ≠ 0
  le : ∀ k σ, frameNorm (A σ) (fun j => σ (w j k)) ≤ Λ
  one_le : 1 ≤ Λ

def HtMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → (∀ (a a' : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → G' ≠ 0 →
      IsMultiHomogeneous a G → IsMultiHomogeneous a' G' → ht w A (G * G') = ht w A G + ht w A G') ∧
    ∀ c : F, c ≠ 0 → ht w A (C c : MvPolynomial (Fin B × Fin N) F) = 0

def HtLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (Λ : ℝ), Lat w A Λ → ∀ (a : Fin B → ℕ) (G : MvPolynomial (Fin B × Fin N) F), G ≠ 0 → IsMultiHomogeneous a G →
      -(cst n Λ * ∑ b, (a b : ℝ)) ≤ ht w A G

def HeightTie : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F) (Λ : ℝ), Lat T.w T.A Λ → ∀ h, T.IsHeight h →
    ∀ (d e : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (c : F), IsChowForm T.imageIdeal T.D d f → 1 ≤ e → c ≠ 0 →
      ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) = h - (harmonic (T.N - 1) : ℝ) / 2 ∧
      h - (Real.log T.n + 1) / 2 ≤ ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ))

structure SimpleAt {F : Type} [Field F] [NumberField F] (T : Tuple F) (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop where
  good : T.IsGoodSection E s
  card : (T.geomPts E (T.linSection E s)).ncard = δ
  inj : (T.toLinSys.baseChange E).InjOnPts (T.geomPts E (T.linSection E s))
  fac : ∃ c : AlgebraicClosure E, c ≠ 0 ∧ spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f =
    C c * ∏ᶠ x ∈ T.geomPts E (T.linSection E s), lin (T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1)

def Bertini : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

def BertiniNF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f →
      (δ : ℤ) = T.del ∧ ∃ Q : MvPolynomial (Fin T.D × Fin T.N) F, Q ≠ 0 ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E),
          aeval (fun p : Fin T.D × Fin T.N => s p.1 p.2) Q ≠ 0 → SimpleAt T δ f E s

section Words

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

def word {t : ℕ} (u : Fin t → Fin N → K) : Module.End K A := (List.ofFn fun i => mul (u i)).prod

def pw {D : ℕ} (s : Fin D → Fin N → K) (α : Fin D →₀ ℕ) : Module.End K A := (List.ofFn fun i => mul (s i) ^ α i).prod

def coordP {B t : ℕ} (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) : MvPolynomial (Fin B × Fin N) K :=
  ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) m)) * ∏ i, X (β i, e i)

end Words

structure Sys (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] where

  N : ℕ

  n : ℕ

  D : ℕ

  T : ℕ

  w : Matrix (Fin N) (Fin n) F

  fr : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  mul : (Fin N → F) →ₗ[F] Module.End F A

  V : ℕ → Submodule F A

  M : ∀ j, Submodule (𝓞 F) (V j)

  nm : ∀ j, HermFam F (V j)

  beta : ℝ

  abelian₂ : ℝ

  Lam0 : ℝ

  LamD : ℝ

  LamT : ℝ

def ClaimS (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h d deg : ℝ) : Prop :=
  0 ≤ 1 - ((T - 1).choose D : ℝ) * δ / d ∧ 1 - ((T - 1).choose D : ℝ) * δ / d ≤ 1 ∧
    (1 - (1 - ((T - 1).choose D : ℝ) * δ / d)) * (T * h - D * (D + 1) * cst n Λ - Real.log Λ₀ - T / 2 * Real.log β) -
      (1 - ((T - 1).choose D : ℝ) * δ / d) * (T * cst n Λ + T / 2 * Real.log β + Real.log ΛD + Real.log ΛT) ≤ deg / d

namespace Sys

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
  (S : Sys F A)

def Short (j : ℕ) (Λ : ℝ) : Prop :=
  ∃ (r : ℕ) (b : Module.Basis (Fin r) F (S.V j)), ∀ i, b i ∈ S.M j ∧ ∀ σ, (S.nm j).nrm σ (b i) ≤ Λ

structure Hyp : Prop where
  one_le : 1 ≤ S.D
  le_T : S.D + 1 ≤ S.T
  lat : Lat S.w S.fr S.abelian₂
  comm : ∀ u v, S.mul u * S.mul v = S.mul v * S.mul u
  full : ∀ j ≤ S.T, IsFull (S.M j)
  stable : ∀ j < S.T, ∀ k, ∀ f ∈ S.M j, ∃ g ∈ S.M (j + 1), (g : A) = S.mul (S.w.col k) f
  bound : ∀ σ, ∀ j < S.T, ∀ (u : Fin S.N → ℂ) (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : Fin S.N × Fin m → S.V (j + 1)),
    (∀ k i, (g (k, i) : A) = S.mul (Pi.single k 1) (f i)) →
      cnrm (S.nm (j + 1)) σ (fun t => u t.1 * c t.2) g ≤ Real.sqrt S.beta * frameNorm (S.fr σ) u * cnrm (S.nm j) σ c f
  one_le_beta : 1 ≤ S.beta
  hermSysHyp_one_le_lambdaZero : 1 ≤ S.Lam0
  one_le_LamD : 1 ≤ S.LamD
  one_le_LamT : 1 ≤ S.LamT
  short0 : S.Short 0 S.Lam0
  shortD : S.Short S.D S.LamD
  shortT : S.Short S.T S.LamT

structure Col where

  j : ℕ

  t : ℕ
  add : j + t = S.T

  β : Fin t → Fin (S.D + 1)

  x : S.V j

def IsCo {d : ℕ} (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F) : Prop := ∀ i (x : S.V S.T), c i x = b.repr x i

def det {d : ℕ} (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col) : MvPolynomial (Fin (S.D + 1) × Fin S.N) F :=
  (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)).det

def Col.HasType {S : Sys F A} (κ : S.Col) (α : Fin S.D →₀ ℕ) : Prop :=
  ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α i

structure Flat (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) where

  ι : A →ₛₗ[algebraMap F E] A'
  indep : ∀ (m : ℕ) (v : Fin m → S.V S.T), LinearIndependent F v → LinearIndependent E fun i => ι (v i)

  mul : (Fin S.N → E) →ₗ[E] Module.End E A'
  comm : ∀ u v, mul u * mul v = mul v * mul u
  mul_ι : ∀ u x, mul (fun k => algebraMap F E (u k)) (ι x) = ι (S.mul u x)

  y : Fin δ → Fin S.N → E
  y_ne : ∀ p, y p ≠ 0

  res : A' →ₗ[E] (Fin δ → E)
  onto : (Submodule.span E (ι '' S.V 0)).map res = ⊤

  U : ℕ → Submodule E A'

  sym : ∀ a, U a →ₗ[E] (MonoDeg (Fin S.D) a × Fin δ → E)
  le : ∀ a < S.T - S.D, U (a + 1) ≤ U a
  ker : ∀ a < S.T - S.D, ∀ x : U a, sym a x = 0 ↔ x.1 ∈ U (a + 1)
  mono : ∀ a < S.T - S.D, ∀ (α : MonoDeg (Fin S.D) a) (l : Fin (S.T - a) → Fin S.N → E), ∀ m ∈ Submodule.span E (ι '' S.V 0),
    ∃ h : pw mul s α.1 (word mul l m) ∈ U a, ∀ α' p,
      sym a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * y p k) * res m p else 0
  div : U (S.T - S.D) = ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (Submodule.span E (ι '' S.V S.D)).map (pw mul s α.1)

def FlatAt (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (s : Fin S.D → Fin S.N → F) : Prop :=
  ∃ (E A' : Type) (_ : Field E) (_ : Algebra F E) (_ : AddCommGroup A') (_ : Module E A')
    (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (c : E), c ≠ 0 ∧
      spec (fun i k => algebraMap F E (s i k)) f = C c * ∏ p, lin (Φ.y p)

structure Shape {d : ℕ} (δ : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0)
    (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d) : Prop where
  x_j : ∀ q, (col (ix q)).j = 0
  x_vec : ∀ q, ((col (ix q)).x : A) = m q.2
  x_type : ∀ q, (col (ix q)).HasType q.1.2.1
  rest : ∀ k, k ∉ Set.range ix → ((col k).j = S.D ∧ ∀ q, (col k).β q ≠ Fin.last S.D) ∨ (col k).j = S.T

def ShortCols {d : ℕ} (col : Fin d → S.Col) : Prop :=
  ∀ k, (col k).x ∈ S.M (col k).j ∧ ∀ σ, (S.nm (col k).j).nrm σ (col k).x ≤
    if (col k).j = 0 then S.Lam0 else if (col k).j = S.D then S.LamD else S.LamT

def deepRank (s : Fin S.D → Fin S.N → F) : ℕ :=
  Module.finrank F (⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) : Submodule F A)

def expo : ℕ := ∑ a ∈ Finset.range (S.T - S.D), (a + S.D - 1).choose (S.D - 1) * (S.T - a)

end Sys

def SlopeBound : Prop :=
  ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]
    (S : Sys F A), S.Hyp → ∀ (δ : ℕ) (f : MvPolynomial (Fin (S.D + 1) × Fin S.N) F) (Q : MvPolynomial (Fin S.D × Fin S.N) F),
      1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible f → Q ≠ 0 →
      (∀ s : Fin S.D → Fin S.N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → S.FlatAt δ f s) →
      0 < Module.finrank F (S.V S.T) ∧
        ClaimS S.T S.D S.n S.abelian₂ S.beta S.Lam0 S.LamD S.LamT δ (ht S.w S.fr f / (((S.D : ℝ) + 1) * δ))
          (Module.finrank F (S.V S.T)) (deg (S.nm S.T) (S.M S.T))

structure GeoHyp {F : Type} [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) : Prop where
  totallyComplex : IsTotallyComplex F
  bir : X.Birational
  nef : IsNef F X.LA
  big : IsBig F X.LA
  nef₂ : IsNef F X.L₂
  big₂ : IsBig F X.L₂
  mulStable : Data.MulStable X
  mulBound : Data.MulBound X fun _ => X.beta
  normsLe : X.NormsLe
  one_le_Lam : 1 ≤ X.abelian₂
  hermSysHyp_one_le_lambdaZero : 1 ≤ Λ₀
  short0 : X.ShortFamily 0 Λ₀
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

def GeoBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ), GeoHyp X Λ₀ → ∀ h, X.IsHeight h →
    Formalism.NormVectorIdentities.Items.HSClaimS 26 X.T X.D X.n 1 X.abelian₂ X.beta X.LamD X.LamT (Real.log Λ₀) X.del h X.d (X.degM X.T)

end GlobalTheory.HSShort
end
end

