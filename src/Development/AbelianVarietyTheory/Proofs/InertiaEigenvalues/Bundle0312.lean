module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTeichmullerOfFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.TameScalar

theorem not_mem_placesOver {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro hv'
  have hc : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem isUnit_inv_sq_sub_one {O : Type} [CommRing O] (u : Oˣ) (h : IsUnit ((u : O) ^ 2 - 1)) :
    IsUnit (((u⁻¹ : Oˣ) : O) ^ 2 - 1) := by
  have e : ((u⁻¹ : Oˣ) : O) ^ 2 - 1 = -(((u⁻¹ : Oˣ) : O) ^ 2 * ((u : O) ^ 2 - 1)) := by
    rw [mul_sub, ← mul_pow, Units.inv_mul]; ring
  rw [e]
  exact (((u⁻¹).isUnit.pow 2).mul h).neg

theorem isUnit_sub_one {O : Type} [CommRing O] (x : O) (h : IsUnit (x ^ 2 - 1)) : IsUnit (x - 1) := by
  have e : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [e] at h
  exact isUnit_of_mul_isUnit_left h

theorem exists_scalar_tmat_of_tame_inertia : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (z : GE N), IsotypicValuationAtRing bkP i s → IsTameInertiaElementAtTwistPrime X i z → ∃ d : (X.O0 i)ˣ, Tmat i s z = (d : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) ∧ IsUnit ((d : X.O0 i) ^ 2 - 1) ∧ IsUnit ((d : X.O0 i) - 1) ∧ eps0 X i z = 1 := by
  intro D N X bkP i s z h hz
  obtain ⟨v, hv, A, hA, hzA, hu, -⟩ := hz
  have hlp : (X.l i).Prime := (X.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (X.l i) := by
    refine not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have h1 : X.rhoS i s z = 1 := h.1 v hl hg A hA z hzA
  have h2 : chiS i s z = if X.side i s then X.delta i z else (X.delta i z)⁻¹ :=
    X.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
  have h3 : IsUnit ((((chiS i s z)⁻¹ : (X.O0 i)ˣ) : X.O0 i) ^ 2 - 1) := by
    rw [h2]
    split_ifs
    · exact isUnit_inv_sq_sub_one _ hu
    · rw [inv_inv]; exact hu
  refine ⟨(chiS i s z)⁻¹, ?_, h3, isUnit_sub_one _ h3, ?_⟩
  · rw [Tmat, h1, Units.val_one]
  · have h4 : cycZ D.host.E N.Om (X.l i) z = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
      rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
      simp
    simp [eps0, h4]

end GlobalTheory.TwSys.TameScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

noncomputable section

namespace GlobalTheory.HWL.IoLayer

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem sepRA' (LL : FinExt l) (e : OCb l) (he : ¬ IsUnit (e - 1)) (t : RA LL)
    (ht : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e = t) (x : RA LL)
    (hx : ∀ k, (t - 1) ^ k ∣ x) : x = 0 := by
  refine sepRA LL e he x ?_
  have h := tmul_sub_one LL (WittVector.teichmuller l e)
  rw [h, ht]
  exact hx

theorem teich_pow (LL : FinExt l) (e : OCb l) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (e ^ l) : RA LL) =
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e) ^ l := by
  have h1 : WittVector.teichmuller l (e ^ l) = (WittVector.teichmuller l e : Ainf l) ^ l := map_pow _ _ _
  rw [h1, Algebra.TensorProduct.tmul_pow, one_pow]

theorem γ₀_X_eq {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL} (R : WSer Γ)
    (g : ↥(GK K)) (c : ℤ_[l]) (hc : (c : ℚ_[l]) = (P.χQ g : ℚ_[l])) :
    R.γ₀ (Γ.resΓ g) X = PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) (binomialSeries ℤ_[l] c) - 1 := by
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  obtain ⟨_, _, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hlin : (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) c := by
    apply Subtype.ext
    have := Γ.χΓ_res g
    rw [P.PD_χ, ← hc] at this
    exact this
  have hact := (GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (R.γ₀ (Γ.resΓ g)) R.φ₀ c h0
    (R.γ₀_comm _) (R.γ₀_X _).1 ((R.γ₀_X _).2.trans hlin)).2
  rw [hact, (_root_.GlobalTheory.Cyc.act_laws l ↥(OL LL)).1, GlobalTheory.Cyc.cyc]


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∃ I : IoS AI R, IoW I := by
  intro l _ P AI K s LL hG Γ R
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨u, hu, huniq⟩ := GlobalTheory.UnramIdem.exists_prod_hom l P K s LL hG Γ.emb Γ.emb_bij
  have he := εroot_sub_not_unit AI s
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 _ he
  obtain ⟨io, hπ, hc⟩ := let_exists
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1) : RA LL) u
  have hπ' := hπ.trans (tmul_sub_one LL _)
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  have h1 : io.comp (letφ R.φ₀) = (φRA LL).comp io := by
    have ht := teich_pow LL (AI.εroot s)
    have he' : ¬ IsUnit (AI.εroot s ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    refine comm_φ l R.φ₀ h0 io u hc (φRA LL) _ hπ' ((φRA_teich LL _).trans ht) ?_
      (sepRA' LL _ he' _ ht)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := hu (c ^ l) m hm hl
      (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hcm, one_pow]) (xb ^ l)
      (tilt_pow hxb l) (shift _ _ o) (fun i => by
        have := DFunLike.congr_fun (Γ.emb_σ (i - 1)) c
        rw [sub_add_cancel, AlgHom.comp_apply, sigma_root K c m hm hl hcm] at this
        rw [this]
        exact ho (i - 1))
    exact e2.trans ((congrArg (φRA LL) e1).trans (φRA_teich LL xb)).symm
  have h2 : ∀ g : ↥(GK K), io.comp (letγ (R.γ₀ (Γ.resΓ g))) = (gRA AI LL (g : GQ l)).comp io := by
    intro g
    obtain ⟨χ, hχ, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
    obtain ⟨⟨io0, hio0, -⟩, -⟩ := GlobalTheory.Cyc.IoMap.main l _ he
    have he' : ¬ IsUnit (AI.actT g (AI.εroot s) - 1) := fun h => he (by
      have := h.map (AI.actT g).symm
      rwa [map_sub, map_one, RingEquiv.symm_apply_apply] at this)
    have e0 := (io_zl LL _ _ he io hπ io0 hio0 (binomialSeries ℤ_[l] (χ g : ℤ_[l]))).trans
      (congrArg (fun w : Ainf l => ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL))
        (io_binomial AI s g _ (hχ g) io0 hio0))
    refine comm_γ _ _ (γ₀_X_eq R g _ (hχ g)) io u hc (gRA AI LL g) _ _ hπ' e0 (gRA_teich AI LL g _) ?_
      (sepRA' LL _ he' _ rfl)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := actT_tilt AI g c (g.2 ⟨c, c.2.1⟩) m hm hl xb hxb
    have e3 := gRA_teich AI LL g xb
    rw [e2] at e3
    exact e1.trans ((congrArg (gRA AI LL g) e1).trans e3).symm
  obtain ⟨I, hI⟩ := assemble R (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) _
    (φRA LL) (fun g : ↥(GK K) => gRA AI LL (g : GQ l)) (inclR_φRA LL) (fun g => inclR_gRA AI LL g)
    (by rw [P.PD_p]; exact (GlobalTheory.HWL.TensorWitt.main l LL).1) io hπ
    (isUnit_inclR LL _ (εroot_ne_one AI s)) h1 h2
  refine ⟨I, fun c m hm hl hcm xb hxb o ho => ?_⟩
  rw [hI, ← cst_apply, hc]
  exact hu c m hm hl hcm xb hxb o ho

end GlobalTheory.HWL.IoLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltration
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem eq_of_pow_eq_of_nilpotent {Q : Type*} [CommRing Q] {a b : Q} {N : ℕ} (hN : IsUnit (N : Q))
    (hb : IsUnit b) (hn : IsNilpotent (a - b)) (h : a ^ N = b ^ N) : a = b := by
  have h1 := (Commute.all a b).geom_sum₂_mul N
  rw [h, sub_self] at h1
  have h2 : IsNilpotent ((∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) - N * b ^ (N - 1)) := by
    have e : (N : Q) * b ^ (N - 1) = ∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i) := by
      rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [e, ← Finset.sum_sub_distrib, ← mem_nilradical]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b i
    rw [hc, mul_assoc]
    exact Ideal.mul_mem_right _ _ (mem_nilradical.2 hn)
  have h3 := h2.isUnit_add_right_of_commute (hN.mul (hb.pow (N - 1))) (Commute.all _ _)
  rw [sub_add_cancel] at h3
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h1)

theorem nilpotent_exp_nsmul {Q : Type*} [CommRing Q] [Module ℚ Q] {x : Q} (hx : IsNilpotent x) (n : ℕ) :
    IsNilpotent.exp ((n : Q) * x) = IsNilpotent.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      ((Commute.all _ _).isNilpotent_mul_left hx) hx, ih, pow_succ]

theorem pow_eq_mul_exp {K Q : Type*} [Field K] [CharZero K] [CommRing Q] [Algebra K Q] {a z t : Q}
    {M N : ℕ} (m : ℕ) (hN : N ≠ 0) (ht : t ^ M = 0) (hz : z ^ N = 1) (hn : IsNilpotent (a - z))
    (ha : a ^ N = ∑ j ∈ Finset.range M, algebraMap K Q ((j.factorial : K)⁻¹) * t ^ j) :
    a ^ m = z ^ m * ∑ j ∈ Finset.range M,
      algebraMap K Q (((m : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
  letI : Algebra ℚ Q := ((algebraMap K Q).comp (algebraMap ℚ K)).toAlgebra
  have hE : ∀ c : K, IsNilpotent.exp (algebraMap K Q c * t) =
      ∑ j ∈ Finset.range M, algebraMap K Q (c ^ j / (j.factorial : K)) * t ^ j := by
    intro c
    rw [IsNilpotent.exp_eq_sum (k := M) (by rw [mul_pow, ht, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_pow, ← mul_assoc, ← map_pow, div_eq_inv_mul, map_mul]
    congr 2
    change algebraMap K Q (algebraMap ℚ K _) = _
    simp
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : IsNilpotent (algebraMap K Q (N : K)⁻¹ * t) :=
    (Commute.all _ _).isNilpotent_mul_left ⟨M, ht⟩
  have hk : ∀ k : ℕ, IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) ^ k =
      ∑ j ∈ Finset.range M, algebraMap K Q (((k : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
    intro k
    rw [← nilpotent_exp_nsmul hx, ← hE, div_eq_mul_inv, map_mul, map_natCast, mul_assoc]
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz hN
  have e : a = z * IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) := by
    refine eq_of_pow_eq_of_nilpotent (N := N) ?_ (hu.mul hx.isUnit_exp) ?_ ?_
    · have := (IsUnit.mk0 _ hN').map (algebraMap K Q)
      rwa [map_natCast] at this
    · have h1 := (Commute.all z _).isNilpotent_mul_left hx.isNilpotent_exp_sub_one
      have h2 := (Commute.all _ _).isNilpotent_sub hn h1
      convert h2 using 1
      ring
    · rw [mul_pow, hz, one_mul, hk, ha]
      simp [div_self hN']
  rw [e, mul_pow, hk]

variable {l : ℕ} [Fact l.Prime]

def filZero (P : LocPrime l) : Subalgebra ℚ_[l] P.R.BdR where
  carrier := {x | x ∈ FilB P 0}
  mul_mem' hx hy := FilB_zero_mul hx hy
  add_mem' hx hy := (FilB P 0).add_mem hx hy
  algebraMap_mem' c := qB_mem c

def filIdeal (P : LocPrime l) (M : ℕ) : Ideal ↥(filZero P) where
  carrier := {x | (x : P.R.BdR) ∈ FilB P (M : ℤ)}
  zero_mem' := (FilB P (M : ℤ)).zero_mem
  add_mem' hx hy := (FilB P (M : ℤ)).add_mem hx hy
  smul_mem' c _ hx := FilB_zero_mul c.2 hx

theorem epsT_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ l ^ s = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow]
  congr 1
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    rfl

theorem ζQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ l ^ s = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ n ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem oB_mem_zero {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) :
    oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem epsT_sub_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (s : ℕ) :
    io AI (epsT AI s) - oB P (P.ζQ s) ∈ FilB P 1 := by
  obtain ⟨y, h1, h2⟩ := T.om (P.ζQ s)
  refine (GlobalTheory.ThetaTie.fil_nat T 1 _).2 ⟨GlobalTheory.MemLoc.aDp l (epsT AI s) - y, ?_, ?_⟩
  · rw [← (_root_.GlobalTheory.MemLoc.thetaD_props l).2.1, map_sub, h2, (_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, epsT,
      WittVector.fontaineTheta_teichmuller, untilt_εroot, AI.ζ_eq, sub_self]
  · rw [map_sub, map_sub, h1, io_apply, GlobalTheory.ThetaTie.eD_ιA]

theorem epsT_pow_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) *
      ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) *
        tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI T s m M
  let π := Ideal.Quotient.mkₐ ℚ_[l] (filIdeal P M)
  have hπ : ∀ x y : ↥(filZero P), π x = π y ↔ (x : P.R.BdR) - y ∈ FilB P (M : ℤ) :=
    fun x y => Ideal.Quotient.eq
  have hnil : ∀ x : ↥(filZero P), (x : P.R.BdR) ∈ FilB P 1 → π x ^ M = 0 := by
    intro x hx
    rw [← map_pow, ← map_zero π, hπ]
    simpa using FilB_pow hx M
  let a : ↥(filZero P) := ⟨io AI (epsT AI s), io_mem AI _⟩
  let z : ↥(filZero P) := ⟨oB P (P.ζQ s), oB_mem_zero T _⟩
  let t : ↥(filZero P) := ⟨tD P, FilB_anti zero_le_one tD_mem⟩
  have hs : ∀ c : ℕ → ℚ_[l], ∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * π t ^ j =
      π (∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, AlgHom.commutes]
  have hc : ∀ c : ℕ → ℚ_[l],
      ((∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j : ↥(filZero P)) : P.R.BdR) =
      ∑ j ∈ Finset.range M, qB P (c j) * tD P ^ j := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl
  have key := pow_eq_mul_exp (K := ℚ_[l]) (a := π a) (z := π z) (t := π t) (M := M) (N := l ^ s) m
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (hnil t tD_mem)
    (by
      rw [← map_pow, ← map_one π]
      congr 1
      apply Subtype.ext
      change oB P (P.ζQ s) ^ l ^ s = 1
      rw [← map_pow, ζQ_pow, map_one])
    ⟨M, by rw [← map_sub]; exact hnil _ (epsT_sub_mem T s)⟩
    (by
      rw [hs (fun j => (j.factorial : ℚ_[l])⁻¹), ← map_pow, hπ, hc]
      change io AI (epsT AI s) ^ l ^ s - _ ∈ _
      rw [← map_pow, epsT_pow]
      exact GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration l P AI T M)
  rw [hs (fun j => ((m : ℚ_[l]) / ((l ^ s : ℕ) : ℚ_[l])) ^ j / (j.factorial : ℚ_[l])), ← map_pow,
    ← map_pow, ← map_mul, hπ, Subalgebra.coe_mul, hc, Nat.cast_pow] at key
  rw [map_pow, map_pow]
  exact key

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatio
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem tc_injective (l : ℕ) [Fact l.Prime] : Function.Injective (tc l) := by
  intro a b hab
  obtain ⟨j, hj⟩ := GlobalTheory.MemLoc.exists_isCrisP l
  have hinj := GlobalTheory.MemLoc.crisP_injective l j hj
  have key : ∀ y : Formalism.Per.Fl l, j (tc l y) =
      algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l)
        (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.tm y)) := by
    intro y
    have := hj.on0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) (Formalism.Per.tm y))
    rw [Subalgebra.coe_algebraMap, ← GlobalTheory.RingIface.tower] at this
    exact this
  have h1 := congrArg j hab
  rw [key, key] at h1
  have h2 := (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2
    (GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l h1)
  have h3 := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h2
  simpa using h3

theorem teich_eq_of_phi_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 →
    φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  intro l _ w' ζ hw h
  have hφ : φc l w' ≠ 0 := ((_root_.GlobalTheory.PMon.Gauss.vr_laws l 1 one_pos le_rfl).2.1 w' hw).1
  have hprod : w' * φc l w' ≠ 0 := by
    intro h0
    rcases _root_.GlobalTheory.PMon.Gauss.acris_mul_eq_zero l _ _ h0 with h0 | h0
    · exact hw h0
    · exact hφ h0
  rw [map_mul, frob_teich] at h
  have h' : (tc l (ζ ^ l) - tc l ζ) * (w' * φc l w') = 0 := by
    linear_combination h
  rcases _root_.GlobalTheory.PMon.Gauss.acris_mul_eq_zero l _ _ h' with h0 | h0
  · exact tc_injective l (sub_eq_zero.1 h0)
  · exact absurd h0 hprod

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestrictiStatement
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ),
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  first | exact @GlobalTheory.ResTr.trace_mir | exact GlobalTheory.ResTr.trace_mir | (intros; apply GlobalTheory.ResTr.trace_mir <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitVector_of_unitFor (E : EtTie W RA RW inclR φR gR πA)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧
      W.one.L.T = Submodule.span O {(e₀ : W.one.V)} ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      W.N W.one = Submodule.span (LetA O n) {e} ∧
      Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
      W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
      ∀ a : LetA O n, a • e = 0 → a = 0 := by
  obtain ⟨-, e₀, h₀, -, -⟩ := E.one_e
  obtain ⟨e, hj, hbij, hφ, hγ, hN⟩ := hU e₀ h₀
  refine ⟨e, e₀, h₀, ?_, hj, hN, ?_, hφ, hγ, fun a ha => ?_⟩
  · have h1 := congrArg (Submodule.map W.one.L.T.subtype) h₀
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_singleton] at h1
    exact h1.symm
  · rw [eq_top_iff]
    rintro z -
    exact Submodule.mem_span_singleton.2 (hbij.2 z)
  · apply W.EE_inj
    apply hbij.1
    simp only
    rw [algebraMap_smul, algebraMap_smul, ha, zero_smul]

end Generic

open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem unitVector : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), Submodule.span ↥(OL LL) {e₀} = ⊤ ∧ W.one.L.T = Submodule.span ↥(OL LL) {(e₀ : W.one.V)} ∧ E.jD W.one e = (1 : RW LL) ⊗ₜ[↥(OL LL)] e₀ ∧ W.N W.one = Submodule.span (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) {e} ∧ Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a • e = 0 → a = 0 := by
  intro D HW F l _ K s LL h
  exact unitVector_of_unitFor _ (unitPart l (D.loc l) (D.locA l) (HW l) (F l) K s LL h)

end GlobalTheory.WachUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusion_injective_saturated_inter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → Function.Injective I.ioE ∧ (∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) ∧ (∀ (x : R.EE) (y : RW LL), I.ioE x = ((l : ℕ) : RW LL) * y → ∃ x', x = ((l : ℕ) : R.EE) * x') ∧ ∀ x : R.EE, (∃ y, inclR LL y = I.ioE x) → ∃ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), algebraMap _ R.EE a = x := by
  first | exact @GlobalTheory.IoInj.ioE_injective_saturated_inter | exact GlobalTheory.IoInj.ioE_injective_saturated_inter | (intros; apply GlobalTheory.IoInj.ioE_injective_saturated_inter <;> assumption)
end

