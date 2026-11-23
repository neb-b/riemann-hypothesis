module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0538

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_truncLog_gal_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk C c hc m
  obtain ⟨M, q, hq1, hq2⟩ := _root_.GlobalTheory.BSP.BK.exists_approx_root l K bk m
  obtain ⟨N, r, hr⟩ := GlobalTheory.T.exists_mul_sub_prime_pow_dvd_E_pow l K bk M m q hq1
  obtain ⟨d, hd⟩ := GlobalTheory.RingBasics.exists_pow_div_factorial l m
  set w₀ : bk.S := ((l : bk.S) ^ M * X - q) * r with hw₀
  have hE : bk.E ∣ w₀ := by
    have e1 : (l : bk.S) ^ M * X - q = -(q - (l : bk.S) ^ M * X) := by ring
    rw [hw₀, e1]
    exact (dvd_neg.2 hq1).mul_right _
  set s' : bk.S := ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : bk.S) * w₀ ^ (j + 1) *
    (l : bk.S) ^ (N * (m - (j + 1))) with hs'
  set s : bk.S := (bk.Ep.natDegree : bk.S) * PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d) * s' with hsdef
  refine ⟨m + N * m, s, ?_, fun g => ?_⟩
  · rw [hsdef]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro j _
    exact ((hE.pow (Nat.succ_ne_zero j)).mul_left _).mul_right _

  set R := Per.AinfP l ⧸ Per.kerP l ^ m
  let qm : Per.AinfP l →+* R := Ideal.Quotient.mk _
  let ι : Per.Ainf l →+* Per.AinfP l := algebraMap (Per.Ainf l) (Per.AinfP l)
  have hev : ∀ x, Per.ev l m (aDp l x) = qm (ι x) := fun x => LogFun.ev_alg m (ι x)
  let I : Ideal R := (Per.kerP l).map qm
  have hI : I ^ m = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have hnil : ∀ x ∈ I, x ^ m = 0 := fun x hx => by
    have := Ideal.pow_mem_pow hx m
    rwa [hI, Ideal.mem_bot] at this
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := fun n hn => by
    have := (GlobalTheory.RingBasics.isUnit_nat l n hn).map qm
    rwa [map_natCast] at this
  obtain ⟨lam, hlam⟩ : ∃ lam : R, (l : R) * lam = 1 := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map qm
    rw [map_natCast] at this
    exact this.exists_right_inv
  let f : bk.S →+* R := qm.comp (ι.comp bk.ev)
  let fσ : bk.S →+* R := qm.comp (ι.comp ((Per.σA (g : GQ l)).comp bk.ev))
  have hEm : ι (bk.ev bk.E) ∈ Per.kerP l := by
    have h0 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    first | exact GlobalTheory.RingIface.alg_mem_kerP _ h0 | exact GlobalTheory.RingIface.alg_mem_kerP h0
  have hfE : f bk.E ∈ I := Ideal.mem_map_of_mem _ hEm
  have hfσE : fσ bk.E ∈ I := by
    refine Ideal.mem_map_of_mem _ ?_
    have := GlobalTheory.RingBasics.ker_σ (g : GQ l) hEm
    rwa [Ideal.mem_comap, GlobalTheory.RingBasics.awayMap_algebraMap₂] at this
  have hdvd : ∀ (φ : bk.S →+* R), φ bk.E ∈ I → ∀ x : bk.S, bk.E ^ m ∣ x → φ x = 0 := by
    intro φ hφ x ⟨y, hy⟩
    rw [hy, map_mul, map_pow, hnil _ hφ, zero_mul]
  have hfr : f q * f r = (l : R) ^ N := by
    have := hdvd f hfE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hfσr : fσ q * fσ r = (l : R) ^ N := by
    have := hdvd fσ hfσE _ hr
    rw [map_sub, map_mul, map_pow, map_natCast] at this
    exact sub_eq_zero.1 this
  have hσq : fσ q = f q := by
    have h := GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil l K bk m M q hq1 hq2 g
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, hev, map_sub, map_sub] at h
    exact sub_eq_zero.1 h
  have hlamN : (l : R) ^ N * lam ^ N = 1 := by rw [← mul_pow, hlam, one_pow]
  have hσr : fσ r = f r := by
    have hu : IsUnit (f q) := isUnit_iff_exists_inv.2 ⟨f r * lam ^ N, by rw [← mul_assoc, hfr, hlamN]⟩
    apply hu.mul_left_cancel
    rw [← hσq, hfσr, hσq, hfr]
  obtain ⟨e, hxe, he1, hlog⟩ := GlobalTheory.T.galois_factor_tilt_log_bdRPlus l C bk.flat (g : GQ l) (c g) (hc g)
  set τ : R := qm (ι (Per.tm e)) with hτ
  have hσX : fσ X = f X * τ := by
    change qm (ι (Per.σA (g : GQ l) (bk.ev X))) = qm (ι (bk.ev X)) * qm (ι (Per.tm e))
    rw [bk.ev_X, ← map_mul, ← map_mul]
    congr 2
    change Per.σA (g : GQ l) (WittVector.teichmuller l _) = _
    rw [GlobalTheory.RingIface.sigA_teich, hxe, map_mul]
  have hσC : ∀ w, fσ (PowerSeries.C w) = f (PowerSeries.C w) := fun w => by
    change qm (ι (Per.σA (g : GQ l) (bk.ev (PowerSeries.C w)))) = qm (ι (bk.ev (PowerSeries.C w)))
    rw [bk.ev_C, bk.gal_w]
  let T : R → R := fun a => ∑ j ∈ Finset.range m, (-1) ^ j * ((m.factorial / (j + 1) : ℕ) : R) * a ^ (j + 1)
  have hT : ∀ (φ : bk.S →+* R) (a : R), φ w₀ = a * (l : R) ^ N → φ s' = (l : R) ^ (N * m) * T a := by
    intro φ a ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hs', map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, ha, T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : N * m = N * (j + 1) + N * (m - (j + 1)) := by
      rw [← mul_add]; congr 1; have := Finset.mem_range.1 hj; omega
    rw [hjm]
    ring
  set A : R := f w₀ * lam ^ N with hAdef
  set B : R := fσ w₀ * lam ^ N with hBdef
  have hA : f w₀ = A * (l : R) ^ N := by rw [hAdef]; linear_combination (-(f w₀)) * hlamN
  have hB' : fσ w₀ = B * (l : R) ^ N := by rw [hBdef]; linear_combination (-(fσ w₀)) * hlamN
  have hAI : A ∈ I := by
    obtain ⟨u, hu⟩ := hE
    rw [hAdef, hu, map_mul]
    exact I.mul_mem_right _ (I.mul_mem_right _ hfE)
  have hbI : τ - 1 ∈ I := by
    have := Ideal.mem_map_of_mem qm (LogFun.mu_mem he1)
    simpa [GlobalTheory.MemLoc.mu, hτ] using this
  have hB : B = A + (τ - 1) + A * (τ - 1) := by
    rw [hBdef, hAdef]
    simp only [hw₀, map_mul, map_sub, map_pow, map_natCast, hσX, hσq, hσr]
    linear_combination (τ - 1) * lam ^ N * hfr + (τ - 1) * hlamN
  have htr : T B = T A + T (τ - 1) := by
    rw [hB]
    exact LogAdd.trunc_add hR m I hI A (τ - 1) hAI hbI
  have hl := GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 hlog m
  have hl2 : (m.factorial : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t) = T (τ - 1) := by
    rw [hl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, map_mul, map_pow, map_sub, map_one, map_natCast, map_neg, hτ]
    rfl
  have hfC : (m.factorial : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) = (l : R) ^ m := by
    have := congrArg (f.comp (PowerSeries.C.comp (algebraMap ℤ_[l] (Wq l bk.a)))) hd
    simpa only [map_mul, map_natCast, map_pow, RingHom.comp_apply] using this
  have hfs' := hT f A hA
  have hfσs' := hT fσ B hB'
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  have e1 : Per.ev l m (aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s)) = fσ s - f s := by
    rw [hev, map_sub, map_sub]; rfl
  have e2 : Per.ev l m ((l : Per.BdRp l) ^ (m + N * m) *
      (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t)) =
      (l : R) ^ (m + N * m) * ((bk.Ep.natDegree : R) * Per.ev l m (aDp l (Per.zA l (c g)) * C.j C.t)) := by
    simp only [map_mul, map_pow, map_natCast]; ring
  rw [map_sub, e1, e2]
  have e3 : fσ s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * fσ s' := by
    rw [hsdef, map_mul, map_mul, map_natCast, hσC]
  have e4 : f s = (bk.Ep.natDegree : R) * f (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) d)) * f s' := by
    rw [hsdef, map_mul, map_mul, map_natCast]
  rw [e3, e4, hfs', hfσs']
  apply (hR _ m.factorial_ne_zero).mul_left_cancel
  rw [mul_zero]
  linear_combination ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (T B - T A)) * hfC -
    ((l : R) ^ (m + N * m) * (bk.Ep.natDegree : R)) * hl2 + ((bk.Ep.natDegree : R) * (l : R) ^ (N * m) * (l : R) ^ m) * htr

end GlobalTheory.BSP.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanVecSLe
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq]
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongr
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

namespace FrobPP

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O)

theorem coeff_natCast_mul_double {R : Type} [CommRing R] (m : ℕ) (G : R⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : R⟦X⟧⟦X⟧) * G)) = (m : R) * coeff n (coeff i G) := by
  rw [← map_natCast (C : R⟦X⟧ →+* R⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : R →+* R⟦X⟧), coeff_C_mul]

theorem ofW_add (w w' : ℕ × ℕ → Wq l a) : ofW t K e (w + w') = ofW t K e w + ofW t K e w' := by
  funext τ; ext i n; simp [coeff_ofW, add_div]

theorem ofW_zero : ofW t K e (0 : ℕ × ℕ → Wq l a) = 0 := by
  funext τ; ext i n; simp [coeff_ofW]

theorem ofW_neg (w : ℕ × ℕ → Wq l a) : ofW t K e (-w) = -ofW t K e w := by
  funext τ; ext i n; simp [coeff_ofW, neg_div]


variable (K e) in
def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) where
  toFun := ofW t K e
  map_zero' := ofW_zero t
  map_add' := ofW_add t

theorem Q_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; obtain ⟨w', rfl⟩ := hy; exact ⟨w + w', ofW_add t w w'⟩

theorem Q_neg {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨w, rfl⟩ := hx; exact ⟨-w, ofW_neg t w⟩

theorem Q_sub {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x - y ∈ QSet t K e := by
  rw [sub_eq_add_neg]; exact Q_add t hx (Q_neg t hy)

theorem Q_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := ⟨0, ofW_zero t⟩

theorem Q_natCast (m : ℕ) : (m : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨Pi.single (0, 0) (m : Wq l a), funext fun τ => ?_⟩
  ext i n
  rw [coeff_ofW, Pi.natCast_apply, ← mul_one ((m : K⟦X⟧⟦X⟧)), coeff_natCast_mul_double]
  rcases i with _ | i <;> rcases n with _ | n <;> simp [dpDen, Pi.single_apply, coeff_one]

theorem Q_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x * y ∈ QSet t K e :=
  _root_.GlobalTheory.CrysPrism.mul_mem_QSet_of_mem l a e O K t x hx y hy

theorem Q_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (k : ℕ) : x ^ k ∈ QSet t K e := by
  induction k with
  | zero => simpa using Q_natCast t (K := K) (e := e) 1
  | succ k ih => rw [pow_succ]; exact Q_mul t ih hx

theorem Q_sum {ι : Type} (s : Finset ι) (f : ι → ZMod a → K⟦X⟧⟦X⟧) (h : ∀ i ∈ s, f i ∈ QSet t K e) :
    ∑ i ∈ s, f i ∈ QSet t K e :=
  Finset.sum_induction f (· ∈ QSet t K e) (fun _ _ => Q_add t) (Q_zero t) h

variable {φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧}

theorem good_add {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x + y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_add t hxQ hyQ, by rw [map_add (f := _)]; exact Q_add t hfxQ hfyQ,
    A + B - x * y * ∑ k ∈ Finset.Ioo 0 l, x ^ (k - 1) * y ^ (l - k - 1) * ((l.choose k / l : ℕ) : ZMod a → K⟦X⟧⟦X⟧),
    ?_, ?_⟩
  · exact Q_sub t (Q_add t hA hB) (Q_mul t (Q_mul t hxQ hyQ) (Q_sum t _ _ fun k _ =>
      Q_mul t (Q_mul t (Q_pow t hxQ _) (Q_pow t hyQ _)) (Q_natCast t _)))
  · rw [map_add (f := _), hxA, hyB, add_pow_prime_eq hl.out]; ring

theorem good_mul {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (hy : y ∈ GoodSet t e φ₂) :
    x * y ∈ GoodSet t e φ₂ := by
  obtain ⟨hxQ, hfxQ, A, hA, hxA⟩ := hx
  obtain ⟨hyQ, hfyQ, B, hB, hyB⟩ := hy
  refine ⟨Q_mul t hxQ hyQ, by rw [map_mul]; exact Q_mul t hfxQ hfyQ,
    A * y ^ l + B * x ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * A * B, ?_, ?_⟩
  · exact Q_add t (Q_add t (Q_mul t hA (Q_pow t hyQ _)) (Q_mul t hB (Q_pow t hxQ _)))
      (Q_mul t (Q_mul t (Q_natCast t _) hA) hB)
  · rw [map_mul, hxA, hyB]; ring

theorem good_zero : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨Q_zero t, by rw [map_zero]; exact Q_zero t, 0, Q_zero t, by simp [zero_pow hl.out.ne_zero]⟩

theorem good_one : (1 : ZMod a → K⟦X⟧⟦X⟧) ∈ GoodSet t e φ₂ :=
  ⟨by simpa using Q_natCast t (K := K) (e := e) 1, by rw [map_one]; simpa using Q_natCast t (K := K) (e := e) 1,
    0, Q_zero t, by simp⟩

theorem good_pow {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ GoodSet t e φ₂) (k : ℕ) : x ^ k ∈ GoodSet t e φ₂ := by
  induction k with
  | zero => rw [pow_zero]; exact good_one t
  | succ k ih => rw [pow_succ]; exact good_mul t ih hx

theorem good_fin (hφC : ∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) (hφX : φ₂ X = (C X + X) ^ l - C (X ^ l))
    (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)) :
    ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂ := by
  have h : (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, Pi.single p (w p) := by
    funext q; rw [Finset.sum_apply]; simp [Pi.single_apply, Finset.sum_ite_eq']
  have h2 : ofW t K e (fun p => if p ∈ s then w p else 0) = ∑ p ∈ s, ofW t K e (Pi.single p (w p)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h]; exact map_sum (ofWHom (K := K) (e := e) t) _ s
  rw [h2]
  refine Finset.sum_induction _ (· ∈ GoodSet t e φ₂) (fun _ _ => good_add t) (good_zero t) fun p _ => ?_
  rw [_root_.GlobalTheory.CrysPrism.ofW_single l a e O K t p.1 p.2 (w p)]
  exact good_mul t (good_mul t (good_mul t (_root_.GlobalTheory.CrysPrism.cstW_mem_GoodSet l a e O K t φ₂ hφC hφX _)
    (good_pow t (_root_.GlobalTheory.CrysPrism.uFam_mem_GoodSet l a e O K t φ₂ hφC hφX) _)) (_root_.GlobalTheory.CrysPrism.dFam_mem_goodSet l a e O K t φ₂ hφC hφX _))
    (_root_.GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet l a e O K t φ₂ hφC hφX (fun x hx y hy => Q_mul t hx hy) _)

theorem ofW_mem_PPSet {w : ℕ × ℕ → Wq l a} (hw : LTo0 l w) : ofW t K e w ∈ PPSet t K e := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨w, hw, fun τ i n => ?_⟩
  rw [coeff_ofW]
  have : ((i.factorial * (n / e).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  exact mul_div_cancel₀ _ this

end Main

theorem frob_mem_PPSet_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ F ∈ PPSet t K e, frob2 φ₂ F ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, frob2 φ₂ F = F ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t sh hsh φ₂ hφC hφsh F hF
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hφX : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    have h2 : φ₂ X = sh (X ^ l) - C (X ^ l) := by rw [h, map_sub, hφsh, hφC, frob_X]
    rw [h2, map_pow, sh_X sh hsh]
  obtain ⟨w, hw, hFw⟩ := hF
  have hF' : F = ofW t K e w := funext fun τ => by
    ext i n
    have h0 : ((dpDen e i n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
    rw [coeff_ofW, eq_div_iff h0, mul_comm]
    exact hFw τ i n
  have hQ := GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower l a e O K t φ₂ (good_fin t hφC hφX) (_root_.GlobalTheory.CrysPrism.coeff_frob2_congr_box l K φ₂ hφC hφX) (fun i n G H => _root_.GlobalTheory.coeff_coeff_pow_eq_of_box K l i n G H)
  obtain ⟨-, ⟨v, hv⟩, B, ⟨b, rfl⟩, hB⟩ := hQ F ⟨w, hF'.symm⟩
  rw [hF'] at hv hB ⊢
  obtain ⟨hv0, hb0⟩ := GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower l a e O K t φ₂ (_root_.GlobalTheory.CrysPrism.emb_algebraMap_injective l a e O K t) (fun x hx y hy => Q_mul t hx hy) hQ
    (_root_.GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero l a e O K t φ₂ hφC hφX) w hw v b hv.symm hB
  exact ⟨hv ▸ ofW_mem_PPSet t hv0, ofW t K e b, ofW_mem_PPSet t hb0, hB⟩

end FrobPP

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  first | exact @GlobalTheory.BSP.norm_hf_g_X_and_φ_le | exact GlobalTheory.BSP.norm_hf_g_X_and_φ_le | (intros; apply GlobalTheory.BSP.norm_hf_g_X_and_φ_le <;> assumption)
end

