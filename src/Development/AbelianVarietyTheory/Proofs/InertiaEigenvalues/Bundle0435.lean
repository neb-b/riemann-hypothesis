module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKCoord

theorem semiBC_injective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Projective A M]
    (hf : Function.Injective f) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun x hx => ?_
  by_contra h0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero A h0
  obtain ⟨w, hw, -⟩ := h B (f.toSemilinearMap.comp φ)
  have h1 := hw x
  rw [hx, map_zero] at h1
  exact hφ (hf (h1.symm.trans (map_zero f).symm))

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

theorem ev_eis_ne_zero (ϖ : PiSys l e) : ϖ.ev a (eis l a e) ≠ 0 := fun h =>
  (ϖ.isUnit_inclW_ev_eis a).ne_zero (by rw [h, map_zero])

theorem ev_injective (ϖ : PiSys l e) : Function.Injective (ϖ.ev a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y, x = eis l a e ^ n * y ∧ ϖ.ev a y = 0 := fun n => by
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, h1, h2⟩ := ih
      obtain ⟨z, rfl⟩ := (ϖ.theta_ev_eq_zero_iff a y).1 (by rw [h2, map_zero])
      rw [map_mul] at h2
      exact ⟨z, by rw [h1]; ring, (mul_eq_zero.1 h2).resolve_left (ev_eis_ne_zero ϖ)⟩
  refine (complete_eis l a e).haus x fun n => ?_
  obtain ⟨y, h1, -⟩ := key n
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) n) Submodule.mem_top

section Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K]
  {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O)

theorem kappa_smul (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w : OW l O) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]

theorem kappa_frob :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def mulZ (o : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => o • x
    map_add' := smul_add o
    map_smul' := fun c x => smul_comm o (algebraMap ℤ_[l] O c) x }

theorem kappa_mulZ (o : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v x => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) x
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

end Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem exists_coord (I : Ident t ϖ P T) {N : Type} [AddCommGroup N] (J : N →+ TW (OW l O) T)
    (h : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) :
    ∃ (c : N →+ Vec K a ι) (hc : ∀ x, c x ∈ P.M),
      (∀ x, J x = I.j (toW t ϖ P ⟨c x, mem_ME_of_mem_M (hc x)⟩)) ∧ ∀ m ∈ P.M, ∃ x, c x = m := by
  choose c hc hJ using fun x => (h (J x)).1 ⟨x, rfl⟩
  refine ⟨AddMonoidHom.mk' c fun x y => ?_, hc, hJ, fun m hm => ?_⟩
  · have h1 := map_add J x y
    rw [hJ, hJ, hJ, ← map_add (f := _), ← map_add (f := _)] at h1
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h1))
  · obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
    rw [hJ] at hx
    exact ⟨x, (congrArg Subtype.val (toW_injective t ϖ P (I.j.injective hx))).symm⟩

theorem eq_of_j_eq (I : Ident t ϖ P T) (f : ZMod a → A O K) (v w : ME P)
    (h : I.j (toW t ϖ P w) = inclO l O (ϖ.iTot t K f) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (f τ : K⟦X⟧) * v.1 τ i := by
  have hm : (fun τ i => (f τ : K⟦X⟧) * v.1 τ i) ∈ ME P :=
    mem_tot.2 fun τ i => mul_mem (le_away _ _ (f τ).2) (mem_tot.1 v.2 τ i)
  have h1 := toW_smul t ϖ P (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) v ⟨_, hm⟩ fun τ => rfl
  rw [← map_smul, ← ϖ.iW_of_mem t K, ← h1] at h
  exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h))


variable (K t ϖ) in
theorem inclO_iTot_E_pow (k : ℕ) : inclO l O (ϖ.iTot t K ((fun _ => EIn l e _) ^ k)) =
    (1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) := by
  rw [map_pow, map_pow, PiSys.iTot_E, inclO_tmul, Algebra.TensorProduct.tmul_pow, one_pow]

theorem eq_of_j_eq_const (I : Ident t ϖ P T) (o : O) (v w : ME P)
    (h : I.j (toW t ϖ P w) = o • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => PowerSeries.C (algebraMap O K o) * v.1 τ i := by
  refine (eq_of_j_eq I (algebraMap O _ o) v w ?_).trans
    (funext fun τ => funext fun i => congrArg (· * v.1 τ i) (algebraMap_eq_C o))
  rwa [AlgHom.commutes, AlgHom.commutes, algebraMap_smul]

theorem eq_of_j_eq_toAc (I : Ident t ϖ P T) (f : (Wq l a)⟦X⟧) (v w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a f) : OW l O) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (toAc t K f τ : K⟦X⟧) * v.1 τ i := by
  refine eq_of_j_eq I (toAc t K f) v w ?_
  rwa [PiSys.iTot_toAc, inclO_tmul]

theorem eq_of_j_eq_phi (I : Ident t ϖ P T) (k : ℕ) {v : Vec K a ι} (hv : v ∈ P.M) (w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) : OW l O) •
      TWmap (frobOW l O) T (I.j (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩))) :
    w.1 = fun τ i => E K l e ^ k * P.phi v τ i := by
  refine eq_of_j_eq I ((fun _ => EIn l e _) ^ k) ⟨_, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ w ?_
  rwa [toW_phi t ϖ P hv, I.j_φ, inclO_iTot_E_pow]

theorem j_frob {EE : FCrys l ↥(OL (ϖ.field a))} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK (ϖ.field a)) → (T →ₗ[ℤ_[l]] T)}
    {j : EE.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises (ϖ.field a) EE (ainfObj _) (ainfId _) T ρ j) (x m : EE.M (ϖ.prism a)) (k : ℕ)
    (h : IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k) :
    j (EE.tr (ϖ.toAinf a) m) = inclW l (ϖ.ev a (eis l a e)) ^ k •
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (EE.tr (ϖ.toAinf a) x)) := by
  let d : ↥(ainfObj (ϖ.field a)).I := ⟨ϖ.ev a (eis l a e), ϖ.theta_ev_eis a⟩
  obtain ⟨n, i, hn⟩ := exists_isFrac (d : (ainfObj (ϖ.field a)).A) (EE.Φ _ d (EE.tr (ϖ.toAinf a) x))
  obtain ⟨r, hr⟩ := EE.Φ_nat (ϖ.toAinf a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ d x m k n i h hn
  have h1 := H.j_φ d (ev_eis_ne_zero ϖ) _ n i hn
  have : IsDomain (ainfObj (ϖ.field a)).A := (ainfId (ϖ.field a)).toMulEquiv.isDomain
  have := EE.proj (ainfObj (ϖ.field a))
  have h0 : (d : (ainfObj (ϖ.field a)).A) ≠ 0 := ev_eis_ne_zero ϖ
  have h2 : (d : (ainfObj (ϖ.field a)).A) ^ i • EE.tr (ϖ.toAinf a) m = (d : (ainfObj (ϖ.field a)).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero h0 h0)))
  exact (smul_eq_of_isUnit j (ϖ.isUnit_inclW_ev_eis a) h2 h1).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I hBS hBK
  letI := zlLat T
  obtain ⟨EE, j, H, him⟩ := hBK
  have h0 : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (j (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (j.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  have h2 := exists_coord I J h1
  obtain ⟨c, hc, hcJ, hs⟩ := h2
  have hi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (ev_injective ϖ)
      (semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  refine ⟨EE, c, fun x y hxy => hi ?_, hc, hs, fun w x => ?_, fun o => ?_, fun x m k h => ?_⟩
  · rw [hcJ, hcJ]
    simp only [hxy]
  · refine eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg j ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (j.map_smulₛₗ _ _))
    have h5 := h4.trans (kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  · have h3 := (hBS l _ _ _ (isAinf_ainfObj (ϖ.field a))).2 _ _ _ _ EE EE j j H H (mulZ T o)
      fun g x => ((T.actT g).map_smul o x).symm
    obtain ⟨U, hU, -⟩ := h3
    refine ⟨U, fun x => eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_⟩
    have h3 := (congrArg j (U.u_tr (ϖ.toAinf a) x)).symm.trans (hU _)
    have h4 := (congrArg (kappa T) h3).trans (kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  · refine eq_of_j_eq_phi I k (hc x) ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg (kappa T) (j_frob H x m k h)).trans (kappa_smul T _ _)
    have h4 := kappa_frob T (j (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ, ← h4]
    exact h3

end GlobalTheory.BKCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdeal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.IdealSubMembership

theorem padicInt_ringHom_ext {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] {J : Ideal A}
    (hlJ : (l : A) ∈ J) [IsHausdorff J A] (φ ψ : ℤ_[l] →+* A) : φ = ψ := by
  ext c
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
  have h1 : c = ((c.appr n : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * d := by rw [← hd]; ring
  have e : φ c - ψ c = (l : A) ^ n * (φ d - ψ d) := by
    rw [h1]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ n)

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} (hJ : J ≤ (⊥ : Ideal A).jacobson) {q : ℕ}
    (hq : (q : A) ∈ J) {x y : A} (hx : x ^ q = x) (hy : y ^ q = y) (hxy : x - y ∈ J) : x = y := by
  set S := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i) with hS
  have hS1 : S * (x - y) = x - y := by
    rw [hS, geom_sum₂_mul, hx, hy]
  have hSJ : S ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy' : Ideal.Quotient.mk J y = Ideal.Quotient.mk J x := (Ideal.Quotient.eq.2 hxy).symm
    have hq' : (q : A ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]; exact hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    simp only [map_mul, map_pow, hxy']
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp
    have : ∀ i ∈ Finset.range q, (Ideal.Quotient.mk J x) ^ i * (Ideal.Quotient.mk J x) ^ (q - 1 - i) =
        (Ideal.Quotient.mk J x) ^ (q - 1) := fun i hi => by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hq', zero_mul]
  have hu : IsUnit (S * (-1) + 1) := (Ideal.mem_jacobson_bot.1 (hJ hSJ)) (-1)
  have h2 : (S * (-1) + 1) * (x - y) = 0 := by linear_combination -hS1
  rw [← sub_eq_zero]
  exact (hu.mul_right_eq_zero).1 h2

variable {l : ℕ} [hl : Fact l.Prime]

theorem sub_mem_I {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (x : bk.S) :
    BK.hf f x - BK.hf g x ∈ B.I := by
  have h : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
    (bk.str.apply_symm_apply _).symm
  rw [← Ideal.Quotient.eq]
  exact (f.f_str _ x h).trans (g.f_str _ x h).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧
      B.I = Ideal.span {BK.hf f bk.E} := by
  intro l _ K bk B f g
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨fun w => ?_, sub_mem_I bk f g X, ?_⟩
  · let φ1 : Wq l bk.a →+* B.A := (BK.hf f).comp C
    let φ2 : Wq l bk.a →+* B.A := (BK.hf g).comp C
    have hz := padicInt_ringHom_ext hlJ (φ1.comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (φ2.comp (algebraMap ℤ_[l] (Wq l bk.a)))
    have ht : ∀ z : Fq l bk.a, φ1 (WittVector.teichmuller l z) = φ2 (WittVector.teichmuller l z) := by
      intro z
      have hq : ((l ^ bk.a : ℕ) : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
        rw [Nat.cast_pow]; exact Ideal.pow_mem_of_mem _ hlJ _ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      have hp : WittVector.teichmuller l z ^ (l ^ bk.a) = WittVector.teichmuller l z := by
        rw [← map_pow, Fq.pow_card]
      refine eq_of_pow_eq_self (IsAdicComplete.le_jacobson_bot _) hq ?_ ?_
        (Ideal.mem_sup_right (sub_mem_I bk f g _))
      · rw [← map_pow, hp]
      · rw [← map_pow, hp]
    have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
      rw [span_teich]; exact Submodule.mem_top
    change φ1 w = φ2 w
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ht z
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, hx]
      exact congrArg (· * φ2 x) (RingHom.congr_fun hz c)
  · rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f]
    change Ideal.map f.f (Ideal.span ({bk.E} : Set bk.prism.A)) = _
    rw [Ideal.map_span]
    exact congrArg Ideal.span (Set.image_singleton (f := f.f) (a := bk.E))

end GlobalTheory.BSP.IdealSubMembership
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem toDisc_injective_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    Function.Injective (toDisc l (s X) ρ) ∧
    (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧
    ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R →
      Function.Injective R := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1
  have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨-, -, -, -, h5⟩ := _root_.GlobalTheory.BSP.TopBasis.basic_facts bk.S A s bk.J ι TB hH
  have hlW : (l : Wq l bk.a) ≠ 0 := WittVector.p_nonzero l (Fq l bk.a)
  have hCl : (C (l : Wq l bk.a) : bk.S) = (l : bk.S) := map_natCast _ l
  have hlS0 : (l : bk.S) ≠ 0 := by
    rw [← hCl]; exact fun h => hlW (C_injective (h.trans (map_zero _).symm))
  have hlA : (l : A) ∈ nonZeroDivisors A := by
    simpa [map_natCast] using h5 _ (mem_nonZeroDivisors_of_ne_zero hlS0)
  have htor : ∀ x : A, (l : A) * x = 0 → x = 0 := fun x hx =>
    (mem_nonZeroDivisors_iff_right.1 hlA x) (by rw [mul_comm]; exact hx)
  have hdvd : ∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x := by
    intro m x y hxy
    rw [← map_pow, _root_.GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c l K bk A s ι TB]
    intro i
    have e := congrArg (TB.c i) hxy
    rw [← map_natCast s l, ← map_pow, TB.c_mul, TB.c_mul] at e
    have hd : X ^ m ∣ (l : bk.S) * TB.c i x := ⟨_, e⟩
    rw [PowerSeries.X_pow_dvd_iff] at hd ⊢
    intro k hk
    have := hd k hk
    rw [← hCl, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hlW
  have small := _root_.GlobalTheory.BSP.mem_J_pow_of_norm_le l K bk A s htor hdvd ρ hρ hρ1
  refine ⟨?_, small, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : ∀ n : ℕ, x ∈ (bk.J.map s) ^ n := fun n => by
      obtain ⟨r, hr, h⟩ := small n
      rw [← Ideal.map_pow]
      exact h x (by rw [hx, norm_zero]; exact hr.le)
    have hHA : IsHausdorff (bk.J.map s) A := TB.complete.toIsHausdorff
    refine hHA.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hmem n
  · intro ρ' hρ' hρ'ρ R hR
    have hρ'1 : ρ' < 1 := lt_of_le_of_lt hρ'ρ hρ1
    have h1 : ‖toDisc l (s X) ρ (s X)‖ ≤ ρ := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ) 1 hρ
    have h1' : ‖toDisc l (s X) ρ' (s X)‖ ≤ ρ' := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ') 1 hρ'
    have h2 : ‖toDisc l (X : bk.S) ρ' (RingHom.id bk.S X)‖ ≤ ρ := by
      have := norm_toDisc_pow_le (l := l) (u := (X : bk.S)) (ρ := ρ') 1 hρ'
      simp only [pow_one] at this
      exact this.trans (by exact_mod_cast hρ'ρ)
    obtain ⟨cD, hc1, -, hcn, -, -, hsup, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 (Disc.map s h1) (isDiscMap_map s h1)
    obtain ⟨cD', hc1', -, hcn', -, -, -, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' hρ'1 (Disc.map s h1') (isDiscMap_map s h1')
    set RS : bk.DS ρ →+* bk.DS ρ' := Disc.map (RingHom.id bk.S) h2 with hRS
    have hRSd : IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) RS := isDiscMap_map _ h2
    have injS : Function.Injective RS := GlobalTheory.T.breuilKisin_closedDisc_restrict_injective l K bk ρ ρ' hρ' hρ'ρ hρ1 RS hRSd
    obtain ⟨-, hlnorm, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ'
    obtain ⟨-, -, hext, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ
    have hlpos : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
    have htorD : ∀ z : bk.DS ρ', l • z = 0 → z = 0 := by
      intro z hz
      rw [nsmul_eq_mul] at hz
      have := hlnorm z
      rw [hz, norm_zero] at this
      exact norm_eq_zero.1 ((div_eq_zero_iff.1 this.symm).resolve_right hlpos.ne')
    have hRc : Continuous R :=
      AddMonoidHomClass.continuous_of_bound R 1 fun x => (hR.norm_le x).trans (one_mul _).ge
    have hRSc : Continuous RS :=
      AddMonoidHomClass.continuous_of_bound RS 1 fun x => (hRSd.norm_le x).trans (one_mul _).ge
    have key : ∀ i y, cD' i (R y) = RS (cD i y) := by
      intro i y
      have hF : Continuous ((cD' i).comp R.toAddMonoidHom) :=
        (AddMonoidHomClass.continuous_of_bound (cD' i) 1 fun z => (hcn' i z).trans (one_mul _).ge).comp hRc
      have hG : Continuous (RS.toAddMonoidHom.comp (cD i)) :=
        hRSc.comp (AddMonoidHomClass.continuous_of_bound (cD i) 1 fun z => (hcn i z).trans (one_mul _).ge)
      have := hext (bk.DS ρ') htorD ((cD' i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i)) hF hG
        (fun a => by
          change cD' i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
          rw [hR.ext, hc1, hc1', hRSd.ext]; rfl)
      exact DFunLike.congr_fun this y
    refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
    have hz : ∀ i, cD i y = 0 := fun i =>
      injS (by rw [← key, hy, map_zero, map_zero])
    exact norm_le_zero_iff.1 (hsup y 0 le_rfl fun i => by rw [hz, norm_zero])

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem card_filter_nonneg_add_reflect (t : ℤ) (ht : 0 ≤ t) (M : Multiset ℤ) (h : ∀ a ∈ M, a < -1 ∨ t < a) :
    Multiset.card (M.filter (0 ≤ ·)) + Multiset.card ((M.map (fun a => t - 1 - a)).filter (0 ≤ ·)) =
      Multiset.card M := by
  rw [Multiset.filter_map, Multiset.card_map]
  have e : M.filter ((fun a => 0 ≤ a) ∘ fun a => t - 1 - a) = M.filter (fun a => ¬ 0 ≤ a) := by
    apply Multiset.filter_congr
    intro a ha
    have := h a ha
    simp only [Function.comp_apply]
    omega
  rw [e, ← Multiset.card_add, Multiset.filter_add_not]

theorem negCount_of_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  intro D bkP i s ι J hH hJ hG v v' hv hv' τ τ' hc
  obtain ⟨τc, h1, h2⟩ := _root_.GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
  have h2' := h2 v' hv' τ' hc
  obtain ⟨a1, a2⟩ := _root_.GlobalTheory.JumpDims.dims_of_mult D bkP i s v hv τ (J τc) hH (hJ v hv τ τc h1)
  obtain ⟨b1, b2⟩ := _root_.GlobalTheory.JumpDims.dims_of_mult D bkP i s v' hv' τ' (J (τc.comp (cj D))) hH (hJ v' hv' τ' _ h2')
  obtain ⟨g1, g2, g3⟩ := hG τc
  have k := card_filter_nonneg_add_reflect (D.R.t : ℤ) (by positivity) (J τc) g3
  rw [a1, a2, b1, b2, g2, Multiset.card_map]
  omega

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem ratio_holds : Ratio := GlobalTheory.PMon.RatioTransport.ratio_of_acris

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingDataStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZeroAdmissible_all_pending_data : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → PairedCharacterCondition.admDZ P := by
  first | exact @GlobalTheory.AdmDepthZero.main | exact GlobalTheory.AdmDepthZero.main | (intros; apply GlobalTheory.AdmDepthZero.main <;> assumption)
end

