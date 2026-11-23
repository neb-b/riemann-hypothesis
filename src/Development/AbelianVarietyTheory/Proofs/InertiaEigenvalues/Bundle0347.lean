module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem pow_mul_sub_mem_of_roots_mod_pow :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ),
      p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I →
        b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  intro R _ I p x y b lam n hx hy hxy hb
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion p x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy'] at hk
  obtain ⟨d, hdd⟩ : ∃ d, d = y - x := ⟨_, rfl⟩
  rw [← hdd] at hk
  have hd : d ∈ I := by
    have e : d = -(x - y) := by rw [hdd]; ring
    rw [e]; exact I.neg_mem hxy
  obtain ⟨h, hh⟩ : ∃ h, h = (Polynomial.derivative p).eval x + k * d := ⟨_, rfl⟩
  have hdh : d * h ∈ I ^ n := by
    have e : d * h = p.eval y - p.eval x := by rw [hk, hh]; ring
    rw [e]; exact sub_mem hy hx
  obtain ⟨j, hjj⟩ : ∃ j, j = b * h - lam := ⟨_, rfl⟩
  have hj : j ∈ I := by
    have e : j = (b * (Polynomial.derivative p).eval x - lam) + b * k * d := by
      rw [hjj, hh]; ring
    rw [e]; exact add_mem hb (I.mul_mem_left _ hd)
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow lam (-j) n
  have e : lam ^ n * (x - y) = -(b * q * (d * h)) - (-j) ^ n * d := by
    have e1 : lam ^ n = (lam - -j) * q + (-j) ^ n := by rw [← hq]; ring
    have e2 : lam - -j = b * h := by rw [hjj]; ring
    have e3 : x - y = -d := by rw [hdd]; ring
    rw [e1, e2, e3]; ring
  rw [e]
  exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ hdh))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (neg_mem hj) n))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxed
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet GlobalTheory.AntiRamConj
open scoped Pointwise

namespace GlobalTheory.ResUnr

theorem cocycle_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R G M) (x : Z1 rho)
    (h σ : G) (hσ : x.1 σ = 0) : x.1 (h * σ * h⁻¹) = rho (h * σ * h⁻¹) (-x.1 h) - (-x.1 h) := by
  have e1 := x.2.2 (h * σ * h⁻¹) h
  have e2 := x.2.2 h σ
  rw [inv_mul_cancel_right, e2, hσ, map_zero, add_zero] at e1
  rw [map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq, add_comm]
  exact e1.symm

theorem res_mem_unrAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (G F Ω) M) (x : Z1 rho)
    (A : ValuationSubring Ω) (m : M) (hm : ∀ σ ∈ Ine (F := F) A, x.1 σ = rho σ m - m) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt rho A := by
  unfold Formalism.GaloisCohomology.unrAt H1ur
  rw [LinearMap.mem_ker]
  unfold ReciprocityTheory.Gal.resH1
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_coboundaries1 _ _).2 ⟨m, fun g => hm g.1.1 (Subgroup.mem_subgroupOf.1 g.2)⟩

theorem mem_of_subsingleton {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : Subsingleton M) (S : Submodule R M) (y : M) :
    y ∈ S := by
  rw [Subsingleton.elim y 0]
  exact S.zero_mem

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

theorem mem_ine_iff_isFrob {B : ValuationSubring N.Om} {σ : GE N} : σ ∈ Ine (F := D.host.E) B ↔ IsFrob B 1 σ := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx => by rw [pow_one]; exact h.2 x hx⟩
  · intro h
    exact ⟨h.1, fun x hx => by have := h.2 x hx; rwa [pow_one] at this⟩

theorem ine_smul {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) (g : GE N) :
    g * σ * g⁻¹ ∈ Ine (F := D.host.E) (g • B) :=
  mem_ine_iff_isFrob.2 (isFrob_smul (mem_ine_iff_isFrob.1 hσ) g)

theorem exists_ine_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    ∃ k : GE N, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P'), ∃ σ₀ ∈ Ine (F := D.host.E) (N.plOm.1 P),
      σ = k * cConj X σ₀ * k⁻¹ := by
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  refine ⟨(cConj X g)⁻¹, fun σ hσ => ?_⟩
  have h3 := ine_smul (cConj_mem_ine X hσ) g
  rw [hg] at h3
  refine ⟨_, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

theorem res_mem_unrAt_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P')
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GE N) M) (x : Z1 rho)
    (hz : ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), x.1 (cConj X σ) = 0) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := D.host.E) (N.plOm.1 P')).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈
      Formalism.GaloisCohomology.unrAt rho (N.plOm.1 P') := by
  obtain ⟨k, hk⟩ := exists_ine_of_conj X h
  refine res_mem_unrAt rho x (N.plOm.1 P') (-x.1 k) fun σ hσ => ?_
  obtain ⟨σ₀, h3, rfl⟩ := hk σ hσ
  exact cocycle_conj rho x k _ (hz _ h3)


set_option maxHeartbeats 800000 in
theorem unrelax : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  intro D N X bkP i s hF K _ _ _ _ hK M R P d φ φ' Q hM hpos hQ x hx hz
  unfold selOn Formalism.GaloisCohomology.SelAll at hx ⊢
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  by_cases h1 : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  · rw [if_pos h1] at hv ⊢
    exact hv
  rw [if_neg h1] at hv ⊢
  by_cases h2 : v ∈ Spl i
  · rw [if_pos (Set.mem_union_left _ h2)]
    exact Submodule.mem_top
  rw [if_neg (by simpa using h2)]
  by_cases h3 : v ∈ Q
  swap
  · rw [if_neg (by simp [h2, h3])] at hv
    exact hv
  obtain ⟨q, hq⟩ := (hQ v).1 h3
  rcases q with a | a
  · haveI : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun y hy => by
      by_contra hn
      exact hy.ne_zero (hK y ((IsLocalRing.mem_maximalIdeal y).2 hn))⟩
    have hT : Tors K K := fun b => ⟨1, fun y hy => by
      rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hy
      rw [hy, zero_smul]⟩
    have hs := (hF M R P d φ φ' hM hpos K (1 : GE N →* Kˣ) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K hT (Tgl i s) (Or.inl rfl)
      a v hq).2.1
    exact mem_of_subsingleton hs _ _
  · rcases hq with rfl | hq
    · refine res_mem_unrAt (red i K (Tgl i s)) x (N.plOm.1 (P (.inr a))) 0 fun σ hσ => ?_
      rw [(hz a σ hσ).1, map_zero, sub_zero]
    · exact res_mem_unrAt_of_conj X hq (red i K (Tgl i s)) x fun σ hσ => (hz a σ hσ).2

end GlobalTheory.ResUnr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientField
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.BaseChange

theorem finrank_eq_of_coord {k K V W : Type} [Field k] [Field K] [Algebra k K] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module K W] (S : Submodule k V) (T : Submodule K W) (J : V →+ W) (L : (K →ₗ[k] k) → W →+ V)
    (hJ : ∀ (c : k) v, J (c • v) = algebraMap k K c • J v) (hL : ∀ lam a v, L lam (a • J v) = lam a • v)
    (hW : ∀ w, ∃ (n : Type) (s : Finset n) (e : n → K) (lam : n → K →ₗ[k] k), w = ∑ j ∈ s, e j • J (L (lam j) w))
    (hS : ∀ v ∈ S, J v ∈ T) (hT : ∀ lam, ∀ w ∈ T, L lam w ∈ S) [Module.Finite k S] :
    Module.Finite K T ∧ Module.finrank K T = Module.finrank k S := by
  let b := Module.finBasis k S
  let w : Fin (Module.finrank k S) → T := fun i => ⟨J (b i), hS _ (b i).2⟩
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro lam
    have h1 : ∑ i, a i • J (b i) = 0 := by
      have := congrArg Subtype.val ha
      simpa [w] using this
    have h2 : ∑ i, lam (a i) • b i = 0 := by
      apply Subtype.ext
      have := congrArg (L lam) h1
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hL] using this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have hJs : ∀ v : S, (⟨J v, hS _ v.2⟩ : T) ∈ Submodule.span K (Set.range w) := by
    intro v
    have : (⟨J v, hS _ v.2⟩ : T) = ∑ i, algebraMap k K (b.repr v i) • w i := by
      apply Subtype.ext
      have e := congrArg (fun x : S => J x) (b.sum_repr v)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, hJ] at e
      simp [w, e]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span K (Set.range w) := by
    intro x _
    obtain ⟨n, s, e, lam, h⟩ := hW x.1
    have : x = ∑ j ∈ s, e j • (⟨J (L (lam j) x.1), hS _ (hT _ _ x.2)⟩ : T) := by
      apply Subtype.ext
      simpa using h
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hJs ⟨_, hT _ _ x.2⟩)
  let B := Module.Basis.mk hli hsp
  exact ⟨Module.Finite.of_basis B, by rw [Module.finrank_eq_card_basis B, Fintype.card_fin]⟩

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →+ M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def cocycleMapOfEquivariant : Z1 rho →+ Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_zero' := Subtype.ext (funext fun g => map_zero u)

def h1MapOfAdditive : H1 rho →+ H1 rho' :=
  QuotientAddGroup.map ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup ((B1 rho').comap (Z1 rho').subtype).toAddSubgroup
    (cocycleMapOfEquivariant rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem res_addH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (h1MapOfAdditive rho rho' u hu he x) =
      h1MapOfAdditive (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem addH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    h1MapOfAdditive rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_addH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₗ[O] K') (r : ℕ)

def vecAdd : (Fin r → K) →+ (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_zero' := funext fun a => map_zero f

theorem vecAdd_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecAdd f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecAdd f r m) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecAdd, repOn, matAct, map_sum, ← Algebra.smul_def]

end Coef

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₗ[X.O0 i] K')

theorem addH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    h1MapOfAdditive ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecAdd f r) continuous_of_discreteTopology (fun g m => vecAdd_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · rw [← one_smul K x]
    generalize (1 : K) = t
    induction hx using Submodule.span_induction generalizing t with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycleMapOfEquivariant _ _ (vecAdd f r) continuous_of_discreteTopology
        (fun g m => vecAdd_repOn f ρ g.1 m) (t • z), c, y, f (t * b), hc, hy, fun g a => ?_, rfl⟩
      change f (t * (z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, algebraMap_smul, algebraMap_smul, mul_smul_comm, map_smul]
    | zero => rw [smul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add, map_add (f := _)]; exact Submodule.add_mem _ (hx t) (hy t)
    | smul a x _ hx => rw [smul_smul]; exact hx _
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

def coefH1 : H1 (repOn ρ (1 : GE N →* Kˣ) K) →+ H1 (repOn ρ (1 : GE N →* K'ˣ) K') :=
  h1MapOfAdditive (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecAdd f r) continuous_of_discreteTopology
    (vecAdd_repOn f ρ)

theorem coefH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : coefH1 i ρ f x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_addH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecAdd f r) continuous_of_discreteTopology
    (vecAdd_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact addH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact addH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem selOn_baseChange (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k]
    [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    (hk : IsRes i k) (hs : Function.Surjective (algebraMap (X.O0 i) k)) (hK : IsRes i K) (Q : Finset (PlE D.host))
    (hfin : Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q)) :
    Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧
      Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  classical
  have hker : RingHom.ker (algebraMap (X.O0 i) k) ≤ RingHom.ker (algebraMap (X.O0 i) K) := fun x hx =>
    hK x (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) hx)
  let ι : k →+* K := (algebraMap (X.O0 i) k).liftOfSurjective hs ⟨algebraMap (X.O0 i) K, hker⟩
  letI : Algebra k K := ι.toAlgebra
  haveI : IsScalarTower (X.O0 i) k K := IsScalarTower.of_algebraMap_eq fun x =>
    ((algebraMap (X.O0 i) k).liftOfRightInverse_comp_apply _ _ ⟨algebraMap (X.O0 i) K, hker⟩ x).symm
  haveI : CompactSpace (GE N) := inferInstance
  refine finrank_eq_of_coord _ _ (coefH1 i ρ ((Algebra.linearMap k K).restrictScalars (X.O0 i)))
    (fun lam => coefH1 i ρ (lam.restrictScalars (X.O0 i))) ?_ ?_ ?_
    (fun v hv => coefH1_mem_selOn bkP i ρ _ Q v hv) (fun lam v hv => coefH1_mem_selOn bkP i ρ _ Q v hv)
  · intro c v
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => ?_))
      exact map_mul (algebraMap k K) c (z.1 g a)
  · intro lam t v
    induction v using Submodule.Quotient.induction_on with
    | H z =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => ?_))
      change lam (t * algebraMap k K (z.1 g a)) = lam t * z.1 g a
      rw [mul_comm t, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  · intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      let b := Module.Basis.ofVectorSpace k K
      have hf : (Set.range z.1).Finite := (isCompact_range z.2.1).finite_of_discrete
      let s := hf.toFinset.biUnion fun m => Finset.univ.biUnion fun a => (b.repr (m a)).support
      refine ⟨_, s, b, b.coord, ?_⟩
      have key : z = ∑ j ∈ s, b j • cocycleMapOfEquivariant _ _ (vecAdd ((Algebra.linearMap k K).restrictScalars (X.O0 i)) _)
          continuous_of_discreteTopology (vecAdd_repOn _ ρ) (cocycleMapOfEquivariant _ _ (vecAdd ((b.coord j).restrictScalars (X.O0 i)) _)
          continuous_of_discreteTopology (vecAdd_repOn _ ρ) z) := by
        refine Subtype.ext (funext fun g => funext fun a => ?_)
        rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Finset.sum_apply]
        change _ = ∑ j ∈ s, b j * algebraMap k K (b.repr (z.1 g a) j)
        have hsub : (b.repr (z.1 g a)).support ⊆ s := fun j hj =>
          Finset.mem_biUnion.2 ⟨z.1 g, by simp, Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hj⟩⟩
        conv_lhs => rw [← b.linearCombination_repr (z.1 g a), Finsupp.linearCombination_apply,
          Finsupp.sum_of_support_subset _ hsub (fun j c => c • b j) (fun j _ => zero_smul _ _)]
        exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
      refine (congrArg (Submodule.mkQ _) key).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      rfl

end GlobalTheory.ResSel.BaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearCoefficientMapCocycles
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResSel.CoefMap

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →ₛₗ[σ] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def semilinearCoefficientMapCocycles : Z1 rho →ₛₗ[σ] Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' c z := Subtype.ext (funext fun g => map_smulₛₗ u _ _)

def slH1 : H1 rho →ₛₗ[σ] H1 rho' :=
  Submodule.mapQ _ _ (semilinearCoefficientMapCocycles rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem res_slH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (slH1 rho rho' u hu he x) =
      slH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem slH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    slH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_slH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₐ[O] K') (r : ℕ)

def vecMap : (Fin r → K) →ₛₗ[(f : K →+* K')] (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_smul' c m := funext fun a => map_mul f _ _

theorem vecMap_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecMap f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecMap f r m) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMap, repOn, matAct, map_sum]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')

theorem slH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    slH1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecMap f r) continuous_of_discreteTopology (fun g m => vecMap_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (vecMap f r) continuous_of_discreteTopology
        (fun g m => vecMap_repOn f ρ g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, smul_eq_mul, map_mul, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem slH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) :
    slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
      (vecMap_repOn f ρ) x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
    (vecMap_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact slH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem cl_mem_selOn_of_algHom (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (K K' : Type)
    [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    [Field K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')
    (Q : Finset (PlE D.host)) (x : Z1 (red i K ρ)) (x' : Z1 (red i K' ρ)) (h : ∀ g a, x'.1 g a = f (x.1 g a))
    (hx : cl x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : cl x' ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  have e : x' = semilinearCoefficientMapCocycles _ _ (vecMap f D.R.r) continuous_of_discreteTopology (vecMap_repOn f ρ) x :=
    Subtype.ext (funext fun g => funext fun a => h g a)
  rw [e]
  exact slH1_mem_selOn bkP i ρ f Q (cl x) hx

end GlobalTheory.ResSel.CoefMap

end
end

