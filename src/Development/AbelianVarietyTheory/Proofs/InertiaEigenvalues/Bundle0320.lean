module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfPrecomplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtalePhiMatrixDecompletionToWach
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl GlobalTheory.FrobDescent

noncomputable section

namespace GlobalTheory.HWL.MatDecompl

section Concrete

open GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
  {LL : FinExt l} {Γ : GamS P K s LL} {R : WSer Γ}

theorem res_eq_one (Γ : GamS P K s LL) (g : ↥(GK K)) (h1 : P.χQ (g : GQ l) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply Subtype.ext
  have := Γ.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at this
  exact this

theorem chi_eq_one (P : LocPrime l) (h : Good K s LL) {g : GQ l} (hg : g ∈ Hinf K) :
    P.χQ g = 1 :=
  ((cyc_basic l P.χQ P.χQ_cyc).2.2 K g
    (IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) (Hinf_le_GK h hg))).2.1 hg

theorem fixH_io (I : IoS AI R) (e : R.EE) : FixH AI K (I.ioE e) :=
  fun g hg h1 => io_fixed I ⟨g, hg⟩ (res_eq_one Γ ⟨g, hg⟩ h1) e

theorem fixH_pi (I : IoS AI R) : FixH AI K (piR AI LL s) := by
  have h := fixH_io I (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) R.EE letπ)
  set_option synthInstance.maxHeartbeats 400000 in
    rw [io_pi I] at h
  exact h

theorem exists_pole_RW (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (x : RW LL) :
    ∃ k, NearPi AI LL s 0 (piR AI LL s ^ k * x) := by
  choose k hk using fun i => exists_pow_mul AI s ((crd (basisO LL) i x).coeff 0)
  refine ⟨Finset.univ.sup k, (nearPi_iff_crd AI LL s _ _).2 fun i => ?_⟩
  obtain ⟨z, hz⟩ := hk i _ (Finset.le_sup (f := k) (Finset.mem_univ i))
  exact ⟨z, by rw [crd_piR_pow, hz, pow_zero, one_mul]⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_near_perfI (h : Good K s LL) (I : IoS AI R) (hI : IoW I) (x : RW LL)
    (hx : FixH AI K x) (m : ℕ) : ∃ u ∈ perfI I l, NearPi AI LL s m (x - u) := by
  obtain ⟨u, hu, hu'⟩ := exists_inv_perfI I l
  refine exists_near AI K LL s _ (algebraMap_mem_perfI I l) u hu hu' (lift_closure _ _ ?_)
    (fun g hg => fixH_pi I g (Hinf_le_GK h hg) (chi_eq_one P h hg))
    x (fun g hg => hx g (Hinf_le_GK h hg) (chi_eq_one P h hg)) m
  rintro y (⟨j, rfl⟩ | ⟨z, hz, k, hk, hl, hzk, hy⟩)
  · refine mem_perfI_of_iterate I l j (l ^ s) _ ?_
    refine (GlobalTheory.TorsionBoundCompare.tmul_iter LL j _).trans ?_
    rw [frob_iter_teich, GlobalTheory.FrobDescent.εroot_pow]
    exact piR_add_one_pow AI LL s
  · have hint : ∀ i, Γ.emb i ⟨z, hz⟩ ∈ OL LL := fun i => by
      refine IsIntegral.of_pow hk ?_
      have : (⟨z, hz⟩ : ↥(K0 K)) ^ k = 1 := Subtype.ext hzk
      rw [← map_pow, this, map_one]
      exact isIntegral_one
    exact mem_perfI_of_io I l (hI ⟨z, hz⟩ k hk hl hzk y hy (fun i => ⟨_, hint i⟩) fun _ => rfl)

theorem mem_fixSub_iff (AI : LocAinf l P) (K : FinExt l) (x : RW LL) :
    x ∈ fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1} ↔ FixH AI K x :=
  mem_fixSub.trans ⟨fun h g h1 h2 => h g ⟨h1, h2⟩, fun h g hg => h g hg.1 hg.2⟩

theorem isUnit_one_add_RW (LL : FinExt l) (x : RW LL) : IsUnit (1 + (l : RW LL) * x) :=
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).1
  isUnit_one_add x

end Concrete

theorem conj_io' {O E A R : Type} [CommRing O] [CommRing E] [CommRing A] [CommRing R]
    [Algebra O E] [Algebra O A] [Algebra O R] {n : Type} [Fintype n] [DecidableEq n]
    (ι : A →ₐ[O] R) (p : ℕ) (τ : A) (φ : R →ₐ[O] R) (io : E →ₐ[O] R) (S : Subring R)
    (ht : IsUnit (ι τ)) (hp : 2 ≤ p)
    (h3 : ∀ m x, Near (ι : A →+* R) p (ι τ) m x → Near (ι : A →+* R) p (ι τ) (p * m) (φ x))
    (meet : ∀ x, (∀ m, Near (ι : A →+* R) p (ι τ) m x) → ∃ r, x = (p : R) * r)
    (comp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) →
      (∀ i, Near (ι : A →+* R) p (ι τ) (i + k) (f i)) →
      ∃ x ∈ S, ∀ m, Near (ι : A →+* R) p (ι τ) (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hφS : ∀ x ∈ S, φ x ∈ S) (hioS : ∀ e, io e ∈ S)
    (hD : ∀ x ∈ modSub (io : E →+* R) p, (φ : R →+* R) x ∈ modSub (io : E →+* R) p)
    (hpole : ∀ x, ∃ k, Near (ι : A →+* R) p (ι τ) 0 ((ι τ) ^ k * x))
    (h2 : ∀ x ∈ S, ∀ m, ∃ u ∈ perfSub (φ : R →+* R) (modSub (io : E →+* R) p) hD,
      Near (ι : A →+* R) p (ι τ) m (x - u))
    (hφt : (p : R) ∣ (ι τ) ^ p - φ (ι τ)) (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    {H : Type} (Q : H → Prop) (g : H → (R →ₐ[O] R)) (hS : ∀ x, x ∈ S ↔ ∀ h, Q h → g h x = x)
    (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (compS : ∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ y ∈ S, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r)
    (compE : ∀ x : ℕ → E, ∃ y, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r)
    (hrefl : ∀ e, IsUnit (io e) → IsUnit e)
    (F : Matrix n n R) (hF : ∀ i j, F i j ∈ S) (hu : IsUnit F) :
    ∃ (V : Matrix n n R) (e : Matrix n n E), IsUnit V ∧ (∀ i j, V i j ∈ S) ∧
      F * V.map φ = V * e.map io := by
  obtain ⟨e, V, h1, h2, h3⟩ := conj_io (ι := (ι : A →+* R)) (φ := (φ : R →+* R))
    (io := (io : E →+* R)) (τ := τ) rfl ht hp h3 meet comp hφS hioS hD hpole h2 hφt hJ
    (fun X Y hX hXY i j => (hS _).2 fun h hh => map_eq_of_mul_eq_one
      (g h : R →+* R) (fun i j => (hS _).1 (hX i j) h hh) hXY i j)
    hsat sep compS compE hrefl F hF hu
  exact ⟨V, e, h2, h1, h3⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem decompletion : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (r : ℕ) (F : Matrix (Fin r) (Fin r) (RW LL)), IsUnit F → (∀ i j, FixH AI K (F i j)) → ∃ (V : Matrix (Fin r) (Fin r) (RW LL)) (F' : Matrix (Fin r) (Fin r) R.EE), IsUnit V ∧ (∀ i j, FixH AI K (V i j)) ∧ F * V.map (φRW LL) = V * F'.map I.ioE := by
  intro l _ P AI K s LL h Γ R I hI r F hu hF
  have hl := GlobalTheory.Decompl.FixL.fixSub_ladic l P AI LL {g | g ∈ GK K ∧ P.χQ g = 1}
  obtain ⟨V, e, h1, h2, h3⟩ := conj_io' (inclR LL) l ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) (φRW LL)
    I.ioE (fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1})
    (isUnit_pi I)
    (Fact.out : l.Prime).two_le
    (near_φ AI LL s)
    (meet_RW AI LL s)
    (GlobalTheory.Decompl.fixSub_nearPi_complete l P AI LL s _ ((mem_fixSub_iff AI K _).2 (fixH_pi I)))
    hl.2.1
    (fun e => (mem_fixSub_iff AI K _).2 (fixH_io I e))
    (stable_io I l)
    (exists_pole_RW AI LL s)
    (fun x hx => exists_near_perfI h I hI x ((mem_fixSub_iff AI K _).1 hx))
    (dvd_pow_sub Fact.out (frob_pi I (P.PD_p K)))
    (isUnit_one_add_RW LL)
    (· ∈ {g | g ∈ GK K ∧ P.χQ g = 1}) (AI.gRW LL)
    (fun _ => mem_fixSub)
    hl.1
    (GlobalTheory.EtaleExact.sep_RW LL)
    hl.2.2
    (series_EE R (P.PD_p K))
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l P AI K s LL h Γ R I hI).2.1
    F
    (fun i j => (mem_fixSub_iff AI K _).2 (hF i j))
    hu
  exact ⟨V, e, h1, fun i j => (mem_fixSub_iff AI K _).1 (h2 i j), h3⟩

end GlobalTheory.HWL.MatDecompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem cycVal_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam lam' : ℕ → ↥(K0 K)) (d d' : ↥(K0 K)) :
    cycVal P K s e (fun a => lam a + lam' a) (d + d') =
      cycVal P K s e lam d + cycVal P K s e lam' d' := by
  unfold cycVal
  simp only [map_add (f := _)]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_add]
  ring

theorem cycVal_neg {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => -lam a) (-d) = -cycVal P K s e lam d := by
  unfold cycVal
  simp only [map_neg]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  ring

theorem cycVal_zero {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ) :
    cycVal P K s e (fun _ => 0) 0 = 0 := by
  simp [cycVal]

theorem exists_cycVal_eq_pow_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (hs : 1 ≤ s) (α : Om l) (hα : α ∈ Ks K s) (hn : ‖α‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hsum := GlobalTheory.ExpImage.Values.sum_zeta P
  have hgeom : ∑ r ∈ Finset.range l, P.ζQ 1 ^ r = 0 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hsum]
    simp
  have hpow : P.ζQ 1 ^ l = 1 := by
    have h := geom_sum_mul (P.ζQ 1) l
    rw [hgeom, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have h0 : P.ζQ 0 = 1 := by
    have h := GlobalTheory.ExpImage.Values.zeta_pow P 0 1
    simpa [hpow] using h.symm
  have h1 : P.ζQ 1 ≠ 1 := by
    intro h
    rw [h] at hsum
    have hc : ((l - 1 : ℕ) : Om l) = -1 := by simpa using hsum
    have hz : ((l : ℕ) : Om l) = 0 := by
      push_cast [Nat.cast_sub hl1.le] at hc
      linear_combination hc
    exact (Nat.cast_ne_zero.mpr (by omega : l ≠ 0)) hz
  have hchain : ∀ j, P.ζQ (j + 1) ^ l = P.ζQ j := fun j => by
    simpa using GlobalTheory.ExpImage.Values.zeta_pow P j 1
  have hmem := _root_.GlobalTheory.Cyc.integers_mem_closure_levels l K P.ζQ h0 h1 hchain s hs α hα hn
  clear hα hn
  induction hmem using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, n, c, hj, hjs, hn', hc, hc1, rfl⟩ := hx
    exact GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq l P K s e j n hj hjs hn' c hc hc1
  | zero =>
    refine ⟨fun _ => 0, 0, fun _ => by simp, by simp, by simp, ?_⟩
    rw [cycVal_zero, mul_zero]
  | add x y _ _ ihx ihy =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ihx
    obtain ⟨lam', d', hlam', hd', hfr', hv'⟩ := ihy
    refine ⟨fun a => lam a + lam' a, d + d', fun a => ?_, ?_, ?_, ?_⟩
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlam a) (hlam' a))
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd hd')
    · simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← hfr, ← hfr']
      ring
    · rw [cycVal_add, hv, hv']
      ring
  | neg x _ ih =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ih
    refine ⟨fun a => -lam a, -d, fun a => by simpa using hlam a, by simpa using hd, ?_, ?_⟩
    · simp only [map_neg, Finset.sum_neg_distrib]
      rw [← hfr]
      ring
    · rw [cycVal_neg, hv]
      ring

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntilt
section
noncomputable section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem iter_tm {l : ℕ} [Fact l.Prime] (j : ℕ) (z : Fl l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[j] (algebraMap (Ainf l) (Acris l) (tm z)) =
      algebraMap (Ainf l) (Acris l) (tm (z ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    refine (GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_
    rw [← pow_mul, ← pow_succ]

theorem acris_cancel {l : ℕ} [Fact l.Prime] (k : ℕ) (u v : Acris l)
    (e : (l : Acris l) ^ k * u = (l : Acris l) ^ k * v) : u = v := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply (GlobalTheory.MemLoc.acris_basic l).2.1
    linear_combination e

theorem series_acris : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  intro l _ h x h2 hx
  obtain ⟨-, -, -, hpw_comp, hpw_nat, -, -⟩ := _root_.GlobalTheory.PSer.PwLaws.pw_laws l
  obtain ⟨c, hdvd, hc⟩ := GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  have hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) =
      (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a := by
    intro j k a
    rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
  have hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x := by
    intro n j
    rw [← hpw_nat, ← hpw_comp, add_comm]
  have shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1) := by
    intro n
    apply acris_cancel (n.toNat + (n+1).toNat)
    have e1 := congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)
    rw [hφl, hφl, iter_tm, hpwj] at e1
    have e2 := hc (n + 1)
    have hh : (n + 1) * (h : ℤ) = n * h + h := by ring
    rw [hh] at e2
    calc (l : Acris l) ^ (n.toNat + (n+1).toNat) * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)
        = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ n.toNat * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)) := by ring
      _ = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ (-n).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by rw [e1]
      _ = (l : Acris l) ^ (n.toNat + 1) * ((l : Acris l) ^ (-(n+1)).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
      _ = _ := by rw [← e2]; ring
  obtain ⟨w, hw, hsum⟩ := _root_.GlobalTheory.twoSided_shift_series l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift
  refine ⟨w, hw, fun Θ hΘ hΘt j => ?_⟩
  have hs := hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)
  have hl : (l : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) =
      (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
    intro n
    have e := congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul,
      map_mul, map_pow, map_pow, map_natCast, hΘt] at e
    rw [RingHom.comp_apply, RingHom.coe_pow]
    have hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ) := by omega
    have ha : (l : ℂ_[l]) ^ n.toNat ≠ 0 := pow_ne_zero _ hl
    rw [hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
    calc Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))
        = ((l : ℂ_[l]) ^ n.toNat)⁻¹ * ((l : ℂ_[l]) ^ n.toNat * Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))) := by
          rw [inv_mul_cancel_left₀ ha]
      _ = _ := by rw [e]; ring
  have hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x))
      ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w) := by
    simpa only [hterm] using hs
  rw [lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_upperRamificationGroup_jumpSum_not_mem :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)),
      lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ →
        ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB
  obtain ⟨hanti, hbot⟩ := _root_.GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot F L
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le _ (wild F L) ⊤ B hanti hbot
  have hjs := _root_.GlobalTheory.PMon.Ram.jumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn
  have hphi := _root_.GlobalTheory.PMon.Ram.card_mul_herbrandPhi_natCast_of_totallyRamified F L h0 n
  simp only [top_inf_eq] at hjs hn
  have hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n := by
    rw [hjs, ← hphi]
    field_simp
  rw [hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]
  cases n with
  | zero =>
    obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by
      by_contra h
      push_neg at h
      exact hB (eq_top_iff.mpr fun σ _ => h σ)
    refine ⟨σ, ?_, hσ⟩
    rw [Nat.cast_zero, h0]
    exact Subgroup.mem_top σ
  | succ k =>
    have hk : ¬ wild F L k ≤ B := (hn k).mp (Nat.lt_succ_self k)
    obtain ⟨σ, hσ, hσB⟩ := SetLike.not_le_iff_exists.mp hk
    refine ⟨σ, ?_, hσB⟩
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this]
    exact hσ

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionModuleExtendingResidueMaps
section
open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun

theorem exists_factor_of_injective {Λ : Type} [CommRing Λ] {X Y J : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup J] [Module Λ J] (hJ : Module.Injective Λ J)
    (g : X →ₗ[Λ] Y) (ψ : X →ₗ[Λ] J) (h : LinearMap.ker g ≤ LinearMap.ker ψ) :
    ∃ u : Y →ₗ[Λ] J, ∀ x, u (g x) = ψ x := by
  have hi : Function.Injective ((LinearMap.ker g).liftQ g le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨u, hu⟩ := hJ.out ((LinearMap.ker g).liftQ g le_rfl) hi ((LinearMap.ker g).liftQ ψ h)
  refine ⟨u, fun x => ?_⟩
  simpa using hu (Submodule.Quotient.mk x)

def powTorsion {Λ : Type} [CommRing Λ] (I : Ideal Λ) (J : Type) [AddCommGroup J] [Module Λ J] : Submodule Λ J where
  carrier := {b | ∃ n : ℕ, ∀ x ∈ I ^ n, x • b = 0}
  zero_mem' := ⟨0, fun x _ => smul_zero x⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, fun x hx => ?_⟩
    rw [smul_add, hn x (Ideal.pow_le_pow_right (Nat.le_add_right n m) hx),
      hm x (Ideal.pow_le_pow_right (Nat.le_add_left m n) hx), add_zero]
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    exact ⟨n, fun x hx => by rw [smul_comm, hn x hx, smul_zero]⟩

theorem residue_smul_eq_zero {Λ : Type} [CommRing Λ] [IsLocalRing Λ] (x : Λ) (hx : x ∈ IsLocalRing.maximalIdeal Λ)
    (a : IsLocalRing.ResidueField Λ) : x • a = 0 := by
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff x).2 hx, zero_mul]

theorem exists_torsion_extension (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P]
    [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P) :
    ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
      ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  let k := ModuleCat.of Λ (IsLocalRing.ResidueField Λ)
  let J := Injective.under k
  let ι : IsLocalRing.ResidueField Λ →ₗ[Λ] J := (Injective.ι k).hom
  have hι : Function.Injective ι := (ModuleCat.mono_iff_injective (Injective.ι k)).1 inferInstance
  have hJ : Module.Injective Λ J := Module.injective_module_of_injective_object Λ J (inj := Injective.injective_under k)
  let m := IsLocalRing.maximalIdeal Λ
  have hmem : ∀ a, ι a ∈ powTorsion m J := fun a =>
    ⟨1, fun x hx => by rw [← map_smul, residue_smul_eq_zero x (by rwa [pow_one] at hx), map_zero]⟩
  refine ⟨ModuleCat.of Λ (powTorsion m J), ι.codRestrict _ hmem, ?_, ?_, ?_⟩
  · rintro ⟨b, n, hn⟩
    exact ⟨n, fun x hx => Subtype.ext (hn x hx)⟩
  · intro a b hab
    exact hι (congrArg Subtype.val hab)
  · intro φ
    obtain ⟨n, hn⟩ := Ideal.exists_pow_inf_eq_pow_smul m N
    have h1 := hn (n + 1) (Nat.le_succ n)
    rw [Nat.add_sub_cancel_left, pow_one] at h1
    let K : Submodule Λ P := m ^ (n + 1) • ⊤
    have hK : K ⊓ N ≤ m • N := by
      rw [show K ⊓ N = _ from h1]
      exact Submodule.smul_mono le_rfl inf_le_right
    have hker : LinearMap.ker (K.mkQ ∘ₗ N.subtype) ≤ LinearMap.ker (ι ∘ₗ φ) := by
      intro y hy
      have hy1 : (y : P) ∈ K := by simpa using hy
      have hy2 : (y : P) ∈ m • N := hK ⟨hy1, y.2⟩
      have hy3 : y ∈ (m • ⊤ : Submodule Λ N) := by
        rwa [Submodule.mem_smul_top_iff]
      have : φ y = 0 := by
        refine Submodule.smul_induction_on (p := fun y => φ y = 0) hy3 ?_ ?_
        · intro r hr z _
          rw [map_smul, residue_smul_eq_zero r hr]
        · intro a b ha hb
          rw [map_add (f := _), ha, hb, add_zero]
      simp [this]
    obtain ⟨u, hu⟩ := exists_factor_of_injective hJ _ _ hker
    have hu2 : ∀ p, (u ∘ₗ K.mkQ) p ∈ powTorsion m J := fun p =>
      ⟨n + 1, fun x hx => by
        rw [← map_smul]
        have : K.mkQ (x • p) = 0 :=
          (Submodule.Quotient.mk_eq_zero K).2 (Submodule.smul_mem_smul hx Submodule.mem_top)
        rw [LinearMap.comp_apply, this, map_zero]⟩
    refine ⟨(u ∘ₗ K.mkQ).codRestrict _ hu2, ?_⟩
    ext y
    exact hu y

end GlobalTheory.SelFun
end

