module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeDegreeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PushoutsMemSpanLocalSelmerPushouts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscreteStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_matrix_relation_discrete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := _root_.GlobalTheory.PMon.UnrDeg.fixed_field_deg l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := _root_.GlobalTheory.PMon.FLOne.flAt_one l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => _root_.GlobalTheory.PMon.ResR.unitM_U0_of_unitM l P r ω hdet' n U hU) (_root_.GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := _root_.GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := _root_.GlobalTheory.exists_frFixed_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => _root_.GlobalTheory.PMon.ResR.mem_span_colv l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (_root_.GlobalTheory.PMon.ResR.latC_smul_of_fr_fixed l P r n U x y _ e he (h3.1 c)))
  exact _root_.GlobalTheory.PMon.Extract.extract l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalIBSubMemFilO
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

namespace GlobalTheory.BKGal.TaylorFil

theorem dpowFil : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ), C.j (dpow x hx n) ∈ Per.FilP l n := by
  intro l _ C x hx n
  have hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x :=
    (congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans
      ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans
        (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))
  have h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]
    simp
  have h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k := by
    intro k
    induction k with
    | zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1
    | succ k ih =>
      rw [pow_succ]
      have := (GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)
      simpa using this
  have h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n := by
    have h4 := congrArg C.j (factorial_mul_dpow x hx n)
    rw [map_mul, map_natCast, map_pow, hj] at h4
    rw [mul_comm, h4, ← alg_mem_FilD_iff, map_pow]
    exact h2 n
  have hu : IsUnit (n.factorial : Per.BdRp l) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h5 := Ideal.mul_mem_right v _ h3
  rwa [mul_assoc, hv, mul_one] at h5

end GlobalTheory.BKGal.TaylorFil

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem pow_mem_filO {C : GlobalTheory.MemLoc.Core l} {x : OB l O} (hx : x ∈ filO O C 1) (j : ℕ) :
    x ^ j ∈ filO O C j := by
  induction j with
  | zero => simpa using toOB_mem_filO_zero (O := O) C 1
  | succ j ih => rw [pow_succ]; simpa using mul_mem_filO ih hx


variable (O K) in
theorem iS_E_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) :
    toOB l O (ϖ.iS O K (EIn l e _)) ∈ filO O C 1 := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add (f := _), map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  have h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l) := by
    have : EIn l e (S O K e) = uIn _ ^ e + (l : S O K e) := Subtype.ext (by simp [E])
    rw [this, map_add (f := _), map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add (f := _), map_pow,
      map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm
  have h2 := dpowFil l C _ hE 1
  rw [dpow_one] at h2
  rw [h1]
  simpa using toOB_tmul_mem_filO (O := O) h2


variable (O) in
theorem muDiv_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    toOB l O (ϖ.muDiv a O g i) ∈ filO O C i :=
  toOB_tmul_mem_filO (dpowFil l C _ _ i)

theorem gal_iSl_sub_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (g : ↥(GK (ϖ.field a)))
    (p : invL l (S O K e)) (hp : (p : K⟦X⟧) ∈ invL l (A O K))
    (hN : ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (p : K⟦X⟧) = E K l e ^ m * h) :
    galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p ∈ filO O C m := by
  obtain ⟨h, hh, k, hk⟩ := hN
  obtain ⟨s, hs⟩ := hp
  set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def
  have hp₀A : p₀ ∈ A O K := by simpa [p₀] using hs
  let q : S O K e := ⟨p₀, A_le_S l e hp₀A⟩
  have hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩ := Subtype.ext (by simp [p₀])
  have hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q) := by
    rw [← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]
  set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef
  have hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D := by
    have h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p) := by
      rw [map_mul, map_pow, map_natCast]
    rw [mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]
  refine mem_filO_of_pow_mul (s := s) ?_
  rw [hD]
  refine mem_filO_of_pow_mul (s := k) ?_
  have hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D) := by
    rw [map_mul, map_pow, map_natCast]
  rw [hk']
  have hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h' := by
    intro i hi
    obtain ⟨h', hh', he⟩ := _root_.GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul l e O K (p : K⟦X⟧) h k m hh hk i hi
    refine ⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩
    have h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p := by
      have h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s) := by simp
      rw [hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    rw [h4, mul_left_comm, he]
    ring
  refine GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_
  obtain ⟨M₀, hM⟩ := ϖ.taylor_S a O K g q r
  obtain ⟨w, hw⟩ := hM (max M₀ 1) (le_max_left _ _)
  have hM1 : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
      ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
        ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]
    congr 1
    rw [PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]
    congr 1
    exact Subtype.ext (by simp [descN])
  refine ⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
    ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩
  · rw [h0] at hw
    rw [hDdef]
    linear_combination (l : OCr l O) ^ k * hw
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)
    obtain ⟨h', hh', he⟩ := hdesc i hi1
    have h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
        ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩ := by
      rw [← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using he)
    rw [mul_left_comm, h2, map_mul, map_mul, map_pow]
    have h5 := mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i)))
      (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))
    rw [← mul_assoc]
    exact filO_anti (by omega) h5

end Main

theorem gal_iB_sub_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg
  have key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m := fun τ =>
    gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ :=
    (galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))
  rw [map_mul, hid, ← mul_sub]
  have h6 := mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)
  rw [zero_add] at h6
  exact h6

end GlobalTheory.BKGal.TaylorFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TameCover

section
variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l)
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

theorem galOA_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (x : OA l O) :
    galOA O (g * h) x = galOA O g (galOA O h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOA_tmul, galOA_tmul, galOA_tmul, GlobalTheory.RingBasics.σA_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def actA (γ : TameGal ↥LL.1 l e a) (f : ZMod a → A ↥(OL LL) ↥LL.1) : ZMod a → A ↥(OL LL) ↥LL.1 :=
  fun τ => ⟨ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) τ, Rot.ringAct_mem rot_A γ (fun σ => (f σ).2) τ⟩

theorem covers_mul {k k' : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hk : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hk' : Covers ↥LL.1 (thetaW a LL) ϖ k' γ') :
    Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ') := by
  intro f f'' hf''
  have h1 := hk' f (actA LL γ' f) (fun τ => rfl)
  have h2 := hk (actA LL γ' f) f'' (fun τ => by
    rw [hf'' τ, map_mul]
    rfl)
  rw [galOA_mul', h1, h2]

theorem covers_of_mem {k : GQ l} (hk : k ∈ ϖ.GfieldInf a) :
    Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) := by
  intro f f' hf'
  have : f' = f := funext fun τ => Subtype.ext (by rw [hf' τ, map_one]; rfl)
  rw [this]
  exact ϖ.galOA_iTot (thetaW a LL) ↥LL.1 hk f

theorem covers_unique {k : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hγ : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hγ' : Covers ↥LL.1 (thetaW a LL) ϖ k γ') : γ = γ' := by
  have key : ∀ f : ZMod a → A ↥(OL LL) ↥LL.1,
      ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) = ringAct γ' (fun σ => (f σ : PowerSeries ↥LL.1)) := by
    intro f
    have h := (hγ f (actA LL γ f) (fun _ => rfl)).symm.trans (hγ' f (actA LL γ' f) (fun _ => rfl))
    have h2 := ϖ.iTot_injective (thetaW a LL) ↥LL.1 h
    funext τ
    exact congrArg Subtype.val (congrFun h2 τ)
  have hs : γ.shift = γ'.shift := by
    by_contra hne
    have h := congrFun (key fun σ => if σ = 0 then 1 else 0) γ.shift
    simp only [ringAct_apply, sub_self] at h
    rw [if_neg (sub_ne_zero.2 hne)] at h
    simp at h
  have hl : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) = ((γ'.left : (↥LL.1)ˣ) : ↥LL.1) := by
    have h := congrArg (fun F => coeff 1 (F 0)) (key fun _ => uIn _)
    have hu : ((uIn (A ↥(OL LL) ↥LL.1) : A ↥(OL LL) ↥LL.1) : PowerSeries ↥LL.1) = X := rfl
    simp only [hu, ringAct_X, coeff_C_mul, coeff_one_X, mul_one] at h
    simpa [TameGal.root] using h
  refine SemidirectProduct.ext (Subtype.ext (Units.ext hl)) ?_
  exact congrArg Multiplicative.ofAdd hs

omit [HasUnr a LL] in
theorem lift_root (a : ℕ) [TameDescentExponentData ↥LL.1 l e a] (ζ : Om l) (hζ : ζ ^ e = 1) :
    ∃ ζK : rootsOfUnity e ↥LL.1, (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) = ζ := by
  obtain ⟨ζ0, h0⟩ := TameDescentExponentData.prim (K := ↥LL.1) l a (e := e)
  have h1 : IsPrimitiveRoot ((ζ0 : ↥LL.1) : Om l) e := h0.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨rootsOfUnity.mkOfPowEq (ζ0 ^ i) (by rw [← pow_mul, mul_comm, pow_mul, h0.pow_eq_one, one_pow]), ?_⟩
  rw [rootsOfUnity.val_mkOfPowEq_coe, ← hi]
  rfl

end

end GlobalTheory.TameCover
end

namespace GlobalTheory.TameCover

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  intro l _ a e _ _ ϖ LL _ _
  have hsucc : e + 1 = l ^ a := TameDescentExponentData.succ_eq (↥LL.1) (l := l) (e := e) (a := a)

  have hroot_mem : ∀ x : Om l, x ^ l ^ a = x → x ∈ (ϖ.field a).1 := fun x hx =>
    ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _ hx)
  have hfix : ∀ h ∈ GK (ϖ.field a), ∀ x ∈ (ϖ.field a).1, h x = x := fun h hh x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
  refine ⟨_root_.GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf l a e ϖ hsucc, ?_, ?_, fun k γ γ' => covers_unique ϖ LL, fun k k' γ γ' => covers_mul ϖ LL,
    fun k => ⟨_root_.GlobalTheory.CoverOne.main l a e ϖ LL k, covers_of_mem ϖ LL⟩, ?_⟩
  · intro k hk
    obtain ⟨m, hm⟩ := _root_.GlobalTheory.FrobAction.galois_pow_frobenius l a k
    have hπ : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
    have hke : k (ϖ.seq 0 ^ e) = ϖ.seq 0 ^ e :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩)
    have hζ : (k (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, hke, div_self (pow_ne_zero _ hπ)]
    obtain ⟨ζK, hζK⟩ := lift_root LL a _ hζ
    refine ⟨⟨ζK, Multiplicative.ofAdd m⟩, _root_.GlobalTheory.BKGal.covers_of_action l a e ϖ LL _ k hk hm ?_⟩
    change k (ϖ.seq 0) = (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0
    rw [hζK, div_mul_cancel₀ _ hπ]
  · intro γ
    have hζ : ((((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)) ^ e = 1 := by
      have h1 : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 γ.left.2, Units.val_one]
      rw [← IntermediateField.coe_pow, h1]
      rfl
    obtain ⟨g, hg1, hg2⟩ := _root_.GlobalTheory.TameFrob.exists_cover l a e ϖ hsucc γ.shift _ hζ
    obtain ⟨h, hh, k, hk, rfl⟩ := _root_.GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf l a e ϖ hsucc g
    have hinj : Function.Injective h := h.injective
    refine ⟨k, hk, _root_.GlobalTheory.BKGal.covers_of_action l a e ϖ LL γ k hk (fun x hx => hinj ?_) (hinj ?_)⟩
    · have h1 := hg1 x hx
      have h2 : (x ^ l ^ γ.shift.val) ^ l ^ a = x ^ l ^ γ.shift.val := by
        rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [hfix h hh _ (hroot_mem _ h2)]
      exact h1
    · have hz : (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) ^ l ^ a = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
        rw [← hsucc, pow_succ, hζ, one_mul]
      rw [hfix h hh _ (mul_mem (hroot_mem _ hz) (ϖ.pi_mem_field a))]
      exact hg2
  · intro k ζ hk
    obtain ⟨hr, -⟩ := _root_.GlobalTheory.BKGal.covers_action l a e ϖ LL k _ hk
    have hr' : ∀ x : Om l, x ^ l ^ a = x → k x = x := fun x hx => by
      rw [hr x hx]
      simp
    obtain ⟨k', hk', h, hh, hkh⟩ := _root_.GlobalTheory.InertiaMod.main l a e ϖ hsucc k hr'
    have hc : Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) := by
      have := covers_mul ϖ LL hk (covers_of_mem ϖ LL hh)
      rwa [mul_one, ← hkh] at this
    refine ⟨k', hk', hc, ?_⟩
    rw [(_root_.GlobalTheory.BKGal.covers_action l a e ϖ LL _ _ hc).2]
    rfl

end GlobalTheory.TameCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDual
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BoundedIndex


set_option maxHeartbeats 1000000 in
theorem h1_reduction_index_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' LA LA' m hm
  obtain ⟨L1, hL1⟩ := GlobalTheory.T.exists_cyclotomic_integral_lattice l P K LL O hO
  obtain ⟨C0, k0, hF⟩ := GlobalTheory.T.bounded_finite_cohomology_quotients hT l P K LL O hO A' LA'
  obtain ⟨Es, hEs⟩ := GlobalTheory.T.exists_finset_primePow_torsion_quotient l LL O hO k0
  have hEs1 : 1 ≤ Es.card := Finset.card_pos.2 ⟨0, hEs 0 (smul_zero _)⟩
  refine ⟨Es.card ^ C0, pow_pos hEs1 _, fun r hI => ?_⟩
  have hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) :=
    GlobalTheory.TateOrth.stable_span_smul_top LA' _
  haveI hX := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A LA r hI
  haveI hY := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A' LA' r hI'
  haveI : Module.Finite O (QuotientCohomology LA' _ hI') := Module.Finite.of_finite
  obtain ⟨f, hker, hf⟩ := GlobalTheory.T.ker_reduction_H1_eq l P K LL O hO A LA r hI
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.tate_pairing_lattice_level_primePow hT l P K LL O hO L1 hL1 A A' LA LA' m hm r hI hI'
  obtain ⟨F, hFc, hFm⟩ := hF r hI'
  have hcardS : Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) =
      Nat.card (LinearMap.range f) := by
    have key : ∀ N : Submodule O (LatticeCohomology LA), LinearMap.ker f = N → Nat.card (LatticeCohomology LA ⧸ N) = Nat.card (LinearMap.range f) := by
      rintro N rfl
      exact Nat.card_congr f.quotKerEquivRange.toEquiv
    exact key _ hker
  rw [hcardS]
  refine ⟨Nat.card_le_card_of_injective _ Subtype.val_injective, ?_⟩
  have hdd : ∀ c, (∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → β y c = 0) → c ∈ LinearMap.range f :=
    GlobalTheory.mem_of_forall_annihilator_annihilator l LL O hO _ _ β (LinearMap.range f)
      (fun c hc => by rw [hβ1 c hc]; exact Submodule.zero_mem _)
  have hA : ∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → y ∈ F ∧ ((l : ℕ) : O) ^ k0 • y = 0 := by
    intro y hy
    obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hFm c'
    refine GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m hm _
      (GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles l K LL O hO A' LA' r hI' c') fun d hd => ?_
    obtain ⟨h, hfd⟩ := hf ⟨d, hd⟩
    have h0 : β (Submodule.Quotient.mk c') (f (Submodule.Quotient.mk ⟨d, hd⟩)) = 0 := hy _ ⟨_, rfl⟩
    exact hβ2 ⟨d, hd⟩ h c' ((congrArg (β (Submodule.Quotient.mk c')) hfd).symm.trans h0)
  calc Nat.card (QuotientCohomology LA _ hI) ≤ Es.card ^ F.card * Nat.card (LinearMap.range f) :=
        GlobalTheory.T.card_le_of_double_annihilator_pairing O _ _ _ β (LinearMap.range f) F Es _ hdd hA hEs
    _ ≤ Es.card ^ C0 * Nat.card (LinearMap.range f) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hEs1 hFc)

end GlobalTheory.BoundedIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinksStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDR_of_links' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsDR) → F₀.IsDR := by
  first | (exact @GlobalTheory.BKLim.isDR_of_links) | (exact GlobalTheory.BKLim.isDR_of_links) | (intros; apply GlobalTheory.BKLim.isDR_of_links  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PushoutsMemSpanLocalSelmerPushoutsStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushouts_mem_span_localSelmerPushouts : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) → ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG → ∀ (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), ∀ c ∈ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE, c ∈ BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst) (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.Pass.LocPush.main | exact GlobalTheory.Pass.LocPush.main | (intros; apply GlobalTheory.Pass.LocPush.main <;> assumption)
end

