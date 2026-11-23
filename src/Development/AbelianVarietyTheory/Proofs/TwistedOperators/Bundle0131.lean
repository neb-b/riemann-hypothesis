module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicVectorSizeSeenOrthogonalSummandLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

def bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : Fin m × Fin n => absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)))

theorem absFin_le_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (i : Fin m) (j : Fin n) : absFin D.host.F v (compFin D.host.F D.host.E v (Y i j)) ≤ bF Y v := by
  unfold bF
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : Fin m × Fin n =>
    absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2))) (Finset.mem_univ (i, j))
  exact h

theorem le_vFin {n : ℕ} (x : Fin n → AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin n) :
    absFin D.host.F v (compFin D.host.F D.host.E v (x i)) ≤ vFin v x := by
  unfold vFin
  have h := Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ i)
  exact h

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_bF_eq_one {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    ∀ᶠ v in Filter.cofinite, bF Y v = 1 := by
  have h : ∀ᶠ v in Filter.cofinite, ∀ p : Fin m × Fin n,
      absFin D.host.F v (compFin D.host.F D.host.E v (Y p.1 p.2)) ≤ 1 :=
    Filter.eventually_all.2 fun p => eventually_absFin_le_one D.host.F (Y p.1 p.2)
  refine h.mono fun v hv => ?_
  unfold bF
  exact max_eq_left (Finset.sup_le fun p _ => hv p)

theorem finite_mulSupport_bF {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) :
    (Function.mulSupport (bF Y)).Finite :=
  (Filter.eventually_cofinite.1 (eventually_bF_eq_one Y)).subset fun _ hv => hv

theorem vFin_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : vFin v (Y *ᵥ x) ≤ bF Y v * vFin v x := by
  rw [vFin]
  refine Finset.sup_le fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact absFin_sum_le D.host.F v _ _ fun j _ =>
    (absFin_mul_le D.host.F v _ _).trans (mul_le_mul' (absFin_le_bF Y v i j) (le_vFin x v j))

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}


open Classical in
def bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F) : ℝ≥0 :=
  max 1 (Finset.univ.sup fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊)

theorem sum_le_bI {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (w : InfinitePlace D.host.F)
    (τ : EmbOver D.host.E w) (i : Fin m) :
    ∑ j, ‖infEmb τ (compInf D.host.F D.host.E w (Y i j))‖₊ ≤ bI Y w := by
  classical
  unfold bI
  refine le_trans ?_ (le_max_right _ _)
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin m =>
    ∑ j, ‖infEmb p.1 (compInf D.host.F D.host.E w (Y p.2 j))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem le_vInf {n : ℕ} (x : Fin n → AE D) (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w) (i : Fin n) :
    ‖infEmb τ (compInf D.host.F D.host.E w (x i))‖₊ ≤ vInf w x := by
  classical
  unfold vInf
  have h := Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, i))
  exact h

theorem vInf_mulVec_le {m n : ℕ} (Y : Matrix (Fin m) (Fin n) (AE D)) (x : Fin n → AE D)
    (w : InfinitePlace D.host.F) : vInf w (Y *ᵥ x) ≤ bI Y w * vInf w x := by
  rw [vInf]
  refine Finset.sup_le fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine (nnnorm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul' (sum_le_bI Y w p.1 p.2) le_rfl)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [nnnorm_mul]
  exact mul_le_mul' le_rfl (le_vInf x w p.1 j)

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem eventually_vFin_seen_eq_one (V : HSp D) (g : GA D V) {ξ : Fin V.rank → D.host.E} (hξ : ξ ≠ 0) :
    ∀ᶠ v in Filter.cofinite, vFin v (seen V g ξ) = 1 := by
  set u : Fin V.rank → AE D := fun i => incA D (ξ i) with hu
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have h1 : ∀ᶠ v in Filter.cofinite, vFin v u ≤ 1 :=
    (Filter.eventually_all.2 fun i => eventually_absFin_le_one D.host.F (u i)).mono fun v hv =>
      Finset.sup_le fun i _ => hv i
  have h2 : ∀ᶠ v in Filter.cofinite, 1 ≤ absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i))) := by
    refine (eventually_absFin_le_one D.host.F (incA D (ξ i)⁻¹)).mono fun v hv => ?_
    have e : incA D (ξ i) * incA D (ξ i)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have := absFin_mul_le D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i)))
      (compFin D.host.F D.host.E v (incA D (ξ i)⁻¹))
    rw [← map_mul, e, map_one, absFin_one] at this
    exact this.trans (mul_le_of_le_one_right' hv)
  refine ((h1.and h2).and ((eventually_bF_eq_one (mt V g⁻¹)).and (eventually_bF_eq_one (mt V g)))).mono
    fun v hv => le_antisymm ?_ ?_
  · refine (vFin_mulVec_le _ u v).trans ?_
    rw [hv.2.1, one_mul]; exact hv.1.1
  · have e : u = mt V g *ᵥ seen V g ξ := by
      rw [seen, Matrix.mulVec_mulVec, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mulVec]
    refine hv.1.2.trans ((le_vFin u v i).trans ?_)
    rw [e]
    refine (vFin_mulVec_le _ _ v).trans ?_
    rw [hv.2.2, one_mul]

theorem seen_emb {S A B : HSp D} (o : GlobalTheory.MixModel.OrthDec S A B) (h : GA D A) (η : Fin A.rank → D.host.E) :
    seen S (o.emb (h, 1)) (o.iA *ᵥ η) = o.jA *ᵥ seen A h η := by
  have e1 : (o.emb (h, 1))⁻¹ = o.emb (h⁻¹, 1) := by rw [← map_inv, Prod.inv_mk, inv_one]
  have e2 : (fun i => incA D ((o.iA *ᵥ η) i)) = o.jA *ᵥ fun i => incA D (η i) := by
    funext i; exact RingHom.map_mulVec (incA D) o.iA η i
  rw [seen, seen, e1, e2, Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.emb_jA, Matrix.mulVec_mulVec]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

variable {D : D7}

theorem vsize_zero {n : ℕ} : vsize (0 : Fin n → AE D) = 0 := by
  have h : ∀ w : InfinitePlace D.host.F, vInf w (0 : Fin n → AE D) = 0 := fun w => by
    classical
    unfold vInf
    refine le_antisymm (Finset.sup_le fun p _ => ?_) zero_le
    simp
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  unfold vsize
  rw [Finset.prod_eq_zero (Finset.mem_univ w) (h w), zero_mul, NNReal.coe_zero]

end GlobalTheory.HtOrth.Transp

namespace GlobalTheory.HtOrth.Transp

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal

theorem vsize_seen_emb_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ,
    ∀ (h : GA D A) (η : Fin A.rank → D.host.E),
      GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  intro D S A B o
  refine ⟨(((∏ w, bI o.jA w) * ∏ᶠ v, bF o.jA v : ℝ≥0) : ℝ), fun h η => ?_⟩
  by_cases hη : η = 0
  · subst hη
    have e : (o.iA *ᵥ (0 : Fin A.rank → D.host.E)) = 0 := Matrix.mulVec_zero _
    have z : ∀ (V : HSp D) (g : GA D V), seen V g 0 = 0 := fun V g => by
      have h0 : (fun i => incA D ((0 : Fin V.rank → D.host.E) i)) = 0 := funext fun i => map_zero _
      rw [seen, h0, Matrix.mulVec_zero]
    rw [e, z, z, vsize_zero]
    exact mul_nonneg (NNReal.coe_nonneg _) (vsize_nonneg _)
  have hη' : o.iA *ᵥ η ≠ 0 := fun e => hη (by
    have := congrArg (o.qA *ᵥ ·) e
    simpa [Matrix.mulVec_mulVec, GlobalTheory.MixModel.OrthDec.qA_iA] using this)
  have f1 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one A h hη)
  have f2 := Filter.eventually_cofinite.1 (eventually_vFin_seen_eq_one S (o.emb (h, 1)) hη')
  rw [seen_emb] at f2 ⊢
  have hf : (Function.mulSupport fun v => vFin v (seen A h η)).Finite := f1.subset fun v hv => hv
  have hf' : (Function.mulSupport fun v => vFin v (o.jA *ᵥ seen A h η)).Finite := f2.subset fun v hv => hv
  unfold vsize
  rw [← NNReal.coe_mul, NNReal.coe_le_coe]
  calc (∏ w, vInf w (o.jA *ᵥ seen A h η)) * ∏ᶠ v, vFin v (o.jA *ᵥ seen A h η)
      ≤ (∏ w, bI o.jA w * vInf w (seen A h η)) * ∏ᶠ v, bF o.jA v * vFin v (seen A h η) :=
        mul_le_mul' (Finset.prod_le_prod' fun w _ => vInf_mulVec_le o.jA _ w)
          (finprod_le_finprod' hf' (((finite_mulSupport_bF o.jA).union hf).subset (Function.mulSupport_mul _ _))
            fun v => vFin_mulVec_le o.jA _ v)
    _ = _ := by
        rw [Finset.prod_mul_distrib, finprod_mul_distrib (finite_mulSupport_bF o.jA) hf, mul_mul_mul_comm]

end GlobalTheory.HtOrth.Transp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlaceProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem idem_eq_locIdem (D : D7) (p : Place D) : idem D p = GlobalTheory.LocWeil.idem D p := by
  rcases p with v | τ
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl]
    rfl
  · rw [GlobalTheory.LocWeil.PlaceIdem.idem_inr]
    simp only [idem, GlobalTheory.LocWeil.PlaceIdem.eInf]
    congr 2

theorem idem_spec : ∀ D : D7, (∀ p, idem D p * idem D p = idem D p) ∧ (∀ p q, p ≠ q → idem D p * idem D q = 0) ∧ (∀ p, cA D (idem D p) = idem D p) ∧ (∀ v : FinPl D, infPart D (idem D (.inl v)) = 0 ∧ finPart D (idem D (.inl v)) ∈ intAE D ∧ IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1))) ∧ (∀ τ : D.what₂.Tau, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ : D.what₂.Tau, idem D (.inr τ)) = 1 ∧ ∀ θ : InfFam D, IsInfFam θ → ∀ τ : D.what₂.Tau, θ τ (infPart D (idem D (.inr τ))) = 1 ∧ ∀ τ' : D.what₂.Tau, τ' ≠ τ → θ τ (infPart D (idem D (.inr τ'))) = 0 := by
  intro D
  have hE : ∀ p, idem D p = GlobalTheory.LocWeil.idem D p := idem_eq_locIdem D
  obtain ⟨hOrth, hTheta, hFinInf, hSum, -, -⟩ := GlobalTheory.LocWeil.PlaceIdem.idem_props D
  simp only [hE]
  refine ⟨fun p => GlobalTheory.LocWeil.idem_mul_self p, fun p q hpq => hOrth p q hpq, fun p => GlobalTheory.LocWeil.cA_idem p,
    ?_, hFinInf, hSum, ?_⟩
  · intro v
    rw [GlobalTheory.LocWeil.PlaceIdem.idem_inl, GlobalTheory.LocWeil.PlaceIdem.infPart_algebraMap,
      GlobalTheory.LocWeil.PlaceIdem.finPart_algebraMap]
    refine ⟨?_, ?_, ⟨singleV D.host.F v 1, rfl, GlobalTheory.LocWeil.PlaceIdem.evalV_single_same _ v,
      fun v' h => GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h⟩⟩
    · exact TensorProduct.zero_tmul _ _
    · apply AddSubgroup.subset_closure
      refine ⟨singleV D.host.F v 1, ?_, 1, ?_⟩
      · simp only [intAf, Set.mem_setOf_eq]
        intro u
        rcases eq_or_ne u v with rfl | h
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_same]
          exact one_mem _
        · rw [GlobalTheory.LocWeil.PlaceIdem.evalV_single_ne _ h]
          exact zero_mem _
      · rfl
  · intro θ hθ τ
    refine ⟨?_, fun τ' h => ?_⟩
    · rw [hTheta θ hθ τ τ, if_pos rfl]
    · rw [hTheta θ hθ τ' τ, if_neg (Ne.symm h)]

end GlobalTheory.PlaceTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem definite_unitary_cocompact :
    ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
      ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c :=
  GlobalTheory.DefiniteQuotient.exists_compact

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfIpEqZero
section
namespace GlobalTheory.LinUnit

section General
open MeasureTheory Matrix GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

noncomputable def fac (g : GL a k) (h : GL b k) : ℝ :=
  nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) *
    nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2)

theorem fac_pos (g : GL a k) (h : GL b k) : 0 < fac g h :=
  mul_pos (Real.rpow_pos_of_pos (nabs_pos' _) _) (Real.rpow_pos_of_pos (nabs_pos' _) _)

theorem om_one_eq (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om 1 g h Φ = fun x => (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) := by
  funext x
  simp [om, fac]

theorem nabs_inv (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by simp [nabs]

theorem fac_sq_mul (g : GL a k) (h : GL b k) :
    fac g h * fac g h * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) = 1 := by
  have hg := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  have hh := nabs_pos' (Matrix.GeneralLinearGroup.det h)
  rw [map_inv, nabs_inv, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le, neg_neg, fac]
  set x := nabs k (Matrix.GeneralLinearGroup.det g)
  set y := nabs k (Matrix.GeneralLinearGroup.det h)
  have e1 : x ^ ((Fintype.card b : ℝ) / 2) * x ^ ((Fintype.card b : ℝ) / 2) * x ^ (-(Fintype.card b : ℝ)) = 1 := by
    rw [← Real.rpow_add hg, ← Real.rpow_add hg]; simp
  have e2 : y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (Fintype.card a : ℝ) = 1 := by
    rw [← Real.rpow_add hh, ← Real.rpow_add hh]; simp
  linear_combination (y ^ (-(Fintype.card a : ℝ) / 2) * y ^ (-(Fintype.card a : ℝ) / 2) *
    y ^ (Fintype.card a : ℝ)) * e1 + e2

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem ip_om_one (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ip ν (om 1 g h Φ) (om 1 g h Φ) = ip ν Φ Φ := by
  have key := integral_comp_mul_mul_volM ν g h⁻¹ (fun x => Φ x * (starRingEnd ℂ) (Φ x))
  have e := fac_sq_mul g h
  rw [om_one_eq]
  unfold ip
  have : ∀ x : Matrix b a k, (fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val) *
      (starRingEnd ℂ) ((fac g h : ℂ) * Φ ((h⁻¹).val * x * g.val)) = ((fac g h * fac g h : ℝ) : ℂ) *
      (Φ ((h⁻¹).val * x * g.val) * (starRingEnd ℂ) (Φ ((h⁻¹).val * x * g.val))) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  simp_rw [this]
  rw [integral_const_mul, key, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, e]
  simp


attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat in
omit [DecidableEq a] [DecidableEq b] in
theorem eq_zero_of_ip_eq_zero {Φ : Matrix b a k → ℂ} (hΦ : Φ ∈ SB (Matrix b a k)) (h0 : ip ν Φ Φ = 0) : Φ = 0 := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨h2, ht⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (Matrix b a k) := inferInstanceAs (BorelSpace (b → a → k))
  have : (volM ν b a).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : Continuous fun x => Complex.normSq (Φ x) := Complex.continuous_normSq.comp hl.continuous
  have hs : HasCompactSupport fun x => Complex.normSq (Φ x) := hK.comp_left (g := Complex.normSq) (by simp)
  have e : ∫ x, Complex.normSq (Φ x) ∂(volM ν b a) = 0 := by
    unfold ip at h0
    simp_rw [Complex.mul_conj] at h0
    rw [integral_complex_ofReal] at h0
    exact_mod_cast h0
  have := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
    (hc.integrable_of_hasCompactSupport hs)).1 e
  have := (hc.ae_eq_iff_eq _ continuous_zero).1 this
  funext x
  exact Complex.normSq_eq_zero.1 (congrFun this x)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem linOm_unitary : ∀ (D : D7) (v : FinPl D) (m n : ℕ) (g : GL (Fin n) (Fv D.host.F v)) (h : GL (Fin m) (Fv D.host.F v)), (∃ r : ℝ, 0 < r ∧ ∀ Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ, linOm v g h Φ = fun x => (r : ℂ) * Φ ((h⁻¹).val * x * g.val)) ∧ ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), linOm v g h Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) ∧ ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (linOm v g h Φ) (linOm v g h Φ) = GlobalTheory.SplitWeil.ip ν Φ Φ ∧ (GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0) := by
  intro D v m n g h
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨⟨fac g h, fac_pos g h, fun Φ => om_one_eq g h Φ⟩, fun Φ hΦ => ⟨?_, fun ν hν => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.SplitWeil.Model.om_mem_SB 1 g h hΦ
  · exact ip_om_one ν g h Φ
  · exact eq_zero_of_ip_eq_zero ν hΦ

end GlobalTheory.LinUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroup
section
noncomputable section

namespace GlobalTheory.OneParamEquivariance

theorem hasDerivAt_apply {F : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (A : ℝ → F →ₗ[ℂ] ℂ) (A' : F →ₗ[ℂ] ℂ) (c : ℝ → F) (c' : F)
    (hA : ∀ x, HasDerivAt (fun t => A t x) (A' x) 0)
    (hc : ∀ f : F →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0) :
    HasDerivAt (fun t => A t (c t)) (A' (c 0) + A 0 c') 0 := by
  let b := Module.finBasis ℂ F
  have e : ∀ (a : F →ₗ[ℂ] ℂ) u, a u = ∑ i, a (b i) * b.coord i u := by
    intro a u
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hA (b i)).fun_mul (hc (b.coord i))
  have e1 : (fun t => A t (c t)) = fun t => ∑ i, A t (b i) * b.coord i (c t) := funext fun t => e _ _
  rw [e1, e A' (c 0), e (A 0) c', ← Finset.sum_add_distrib]
  exact this

theorem equivariant_of_generator : ∀ (σ Z H : Type) [Finite σ] [AddCommGroup H] [Module ℂ H] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : ℝ → Module.End ℂ (Z → ℂ)) (L : Module.End ℂ (MvPolynomial σ ℂ)) (U : ℝ → Module.End ℂ H) (B : MvPolynomial σ ℂ →ₗ[ℂ] H) (Λ : Set (H →ₗ[ℂ] ℂ)), Function.Injective pt → R 0 = 1 → (∀ s t, R (s + t) = R s * R t) → (∀ t φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R t (pt φ) = pt ψ) → (∀ φ z, HasDerivAt (fun t : ℝ => R t (pt φ) z) (pt (L φ) z) 0) → U 0 = 1 → (∀ s t, U (s + t) = U s * U t) → (∀ x, (∀ l ∈ Λ, l x = 0) → x = 0) → (∀ l ∈ Λ, ∀ t, l ∘ₗ U t ∈ Λ) → (∀ l ∈ Λ, ∀ φ, HasDerivAt (fun t : ℝ => l (U t (B φ))) (l (B (L φ))) 0) → ∀ φ φ', pt φ' = R 1 (pt φ) → B φ' = U 1 (B φ) := by
  intro σ Z H _ _ _ pt R L U B Λ hpt hR0 hR hdeg hder hU0 hU hsep hΛ hB φ φ' hφ
  choose ρ hρd hρ using hdeg
  have hρ0 : ∀ ψ, ρ 0 ψ = ψ := fun ψ => hpt (by rw [← hρ, hR0]; rfl)
  have hρadd : ∀ s t ψ, ρ (s + t) ψ = ρ s (ρ t ψ) := fun s t ψ => hpt (by
    rw [← hρ, ← hρ, ← hρ, hR]; rfl)
  have key : ∀ l ∈ Λ, ∀ ψ, HasDerivAt (fun s : ℝ => l (U (-s) (B (ρ s ψ)))) 0 0 := by
    intro l hl ψ
    let F := MvPolynomial.restrictTotalDegree σ ℂ (max ψ.totalDegree (L ψ).totalDegree)
    have hc : ∀ s, ρ s ψ ∈ F := fun s =>
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hρd s ψ).trans (le_max_left _ _))
    have hy : L ψ ∈ F := (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)
    have h1 := GlobalTheory.CompactIntertwiner.hasDerivAt_dual_of_sep (F := F)
      (fun z => (LinearMap.proj z ∘ₗ pt) ∘ₗ F.subtype)
      (fun x hx => Subtype.ext (hpt (by rw [Submodule.coe_zero, map_zero]; exact funext hx)))
      (fun s => ⟨ρ s ψ, hc s⟩) ⟨L ψ, hy⟩ (fun z => by
        have := hder ψ z
        simp only [hρ] at this
        exact this)
    have h2 : ∀ x : F, HasDerivAt (fun s : ℝ => (l ∘ₗ U (-s) ∘ₗ B ∘ₗ F.subtype) x)
        ((-(l ∘ₗ B ∘ₗ L ∘ₗ F.subtype)) x) 0 := by
      intro x
      have h3 : HasDerivAt (fun t : ℝ => l (U t (B x))) (l (B (L x))) (-0) := by
        rw [neg_zero]; exact hB l hl x
      have h4 := h3.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      rw [neg_one_smul] at h4
      exact h4
    have h5 := hasDerivAt_apply _ _ _ _ h2 h1
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.neg_apply, hρ0, neg_zero, hU0,
      Module.End.one_apply, neg_add_cancel] at h5
    exact h5
  have hconst : ∀ l ∈ Λ, l (U (-1) (B (ρ 1 φ))) = l (B φ) := by
    intro l hl
    have hd : ∀ t₀ : ℝ, HasDerivAt (fun t : ℝ => l (U (-t) (B (ρ t φ)))) 0 t₀ := by
      intro t₀
      have h1 : HasDerivAt (fun s : ℝ => (l ∘ₗ U (-t₀)) (U (-s) (B (ρ s (ρ t₀ φ))))) 0 (t₀ - t₀) := by
        rw [sub_self]; exact key _ (hΛ l hl _) _
      have h2 := h1.comp_sub_const t₀ t₀
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have e : -t₀ + -(t - t₀) = -t := by ring
      beta_reduce
      rw [← hρadd, sub_add_cancel, LinearMap.comp_apply, ← Module.End.mul_apply, ← hU, e]
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
    simpa [hρ0, hU0] using this
  have h1 : U (-1) (B (ρ 1 φ)) = B φ :=
    sub_eq_zero.1 (hsep _ fun l hl => by rw [map_sub, hconst l hl, sub_self])
  have h2 : φ' = ρ 1 φ := hpt (by rw [hφ, hρ])
  rw [← h1, ← Module.End.mul_apply, ← hU, add_neg_cancel, hU0, h2]
  rfl

end GlobalTheory.OneParamEquivariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist

theorem exists_thG_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks R h0 hf hm fun i t => ((h i t).1 (e i t)).1
  exact ⟨th i t, h1 i t⟩

end GlobalTheory.Twist
end

