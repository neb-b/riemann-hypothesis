module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransfer
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.NewPrime.ScalarChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (hs : ∀ (a : R) (m : M), a • m = σ a • m)
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (he : ∀ g m, rho g m = rho' g m)

def idSl : M →ₛₗ[σ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := hs c m

def tr : H1 rho →ₛₗ[σ] H1 rho' :=
  slH1 rho rho' (idSl σ hs) continuous_id he

def back (z : Z1 rho') : Z1 rho :=
  ⟨z.1, z.2.1, fun g h => by rw [z.2.2, he]⟩

theorem tr_back (z : Z1 rho') :
    tr σ hs rho rho' he (Submodule.Quotient.mk (back rho rho' he z)) = Submodule.Quotient.mk z :=
  congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem tr_injective : Function.Injective (tr σ hs rho rho' he) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles rho rho' (idSl σ hs) continuous_id he z) : H1 rho') = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    rw [he]
    exact hm g

theorem res_tr {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (tr σ hs rho rho' he x) =
      tr σ hs (rho.comp phi) (rho'.comp phi) (fun g m => he (phi g) m) (resH1 rho phi hphi x) :=
  res_slH1 rho rho' (idSl σ hs) continuous_id he phi hphi x

theorem of_tr_mem_ur (J : Subgroup Γ) (x : H1 rho) (hx : tr σ hs rho rho' he x ∈ H1ur rho' J) : x ∈ H1ur rho J := by
  have h0 : resH1 rho' J.subtype continuous_subtype_val (tr σ hs rho rho' he x) = 0 := hx
  have h1 := res_tr σ hs rho rho' he J.subtype continuous_subtype_val x
  exact tr_injective σ hs (rho.comp J.subtype) (rho'.comp J.subtype) (fun g m => he g.1 m)
    (h1.symm.trans (h0.trans (map_zero _).symm))

end General

section Coef

variable {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ'] (φ : Λ →ₐ[O] Λ')
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

include hY in
theorem algebraMap_smul (c : O) (y : Y) : algebraMap O Λ c • y = algebraMap O Λ' c • y := by
  rw [hY, φ.commutes]

include hY in
theorem vec_smul {r : ℕ} (a : Λ) (m : Fin r → Y) : a • m = φ a • m :=
  funext fun c => hY a (m c)

include hY in
theorem repOn_eq_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (κ' : Γ →* Λ'ˣ)
    (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) (g : Γ) (m : Fin r → Y) :
    repOn ρ κ Y g m = repOn ρ κ' Y g m := by
  funext a
  change ((κ g : Λˣ) : Λ) • ∑ j, algebraMap O Λ ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j =
    ((κ' g : Λ'ˣ) : Λ') • ∑ j, algebraMap O Λ' ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j
  simp only [algebraMap_smul φ hY]
  rw [hY, hκ]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ'] [Algebra (X.O0 i) Λ']
  (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ) (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ))
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y]
  (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

abbrev trG : H1 (repOn ρ κ Y) →ₛₗ[(φ : Λ →+* Λ')] H1 (repOn ρ κ' Y) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)

abbrev trL (v : PlE D.host) :
    H1 ((repOn ρ κ Y).comp (DecV N v).subtype) →ₛₗ[(φ : Λ →+* Λ')] H1 ((repOn ρ κ' Y).comp (DecV N v).subtype) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
    (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m)

theorem trL_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ Y).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ Y v) : trL i ρ φ κ κ' hκ hY v x ∈ bkOn bkP i ρ κ' Y v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id
        (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → Y) g a) = _
      rw [hz, algebraMap_smul φ hY]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem exists_mem_bkOn (v : PlE D.host) (x' : H1 ((repOn ρ κ' Y).comp (DecV N v).subtype))
    (hx : x' ∈ bkOn bkP i ρ κ' Y v) : ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = x' := by
  by_cases hv : v ∈ placesOver D.host.E (X.l i)
  · have H : ∀ a : Λ', ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = a • x' := by
      unfold bkOn at hx
      rw [dite_eq_left hv] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro a
        obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
        refine ⟨Submodule.Quotient.mk (back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z)), ?_,
          tr_back _ _ _ _ _ _⟩
        unfold bkOn
        rw [dite_eq_left hv]
        refine Submodule.subset_span ⟨back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z), c, y, a • b, hc, hy,
            fun g e => ?_, rfl⟩
        change a • ((z : ↥(DecV N v) → Fin r → Y) g e) = _
        rw [hz, algebraMap_smul φ hY, smul_comm]
      | zero => exact fun a => ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero]⟩
      | add x y _ _ hx hy =>
        intro a
        obtain ⟨w, hw, e⟩ := hx a
        obtain ⟨w', hw', e'⟩ := hy a
        exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [map_add (f := _), e, e', smul_add]⟩
      | smul c x _ hx =>
        intro a
        obtain ⟨w, hw, e⟩ := hx (a * c)
        exact ⟨w, hw, by rw [e, mul_smul]⟩
    simpa using H 1
  · unfold bkOn at hx
    rw [dite_eq_right hv, Submodule.mem_bot] at hx
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hx]⟩

theorem trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y)) (hx : x ∈ selOn bkP i ρ κ Y Q) :
    trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact trL_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem of_trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y))
    (hx : trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q) : x ∈ selOn bkP i ρ κ Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  have e := res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x
  have hv' : trL i ρ φ κ κ' hκ hY v (resH1 (repOn ρ κ Y) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ∈
      Formalism.GaloisCohomology.bkCond (repOn ρ κ' Y) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ' Y) v := e ▸ hv
  unfold Formalism.GaloisCohomology.bkCond at hv' ⊢
  split_ifs at hv' ⊢ with h1 h2
  · obtain ⟨w, hw, e'⟩ := exists_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv'
    rwa [← tr_injective _ _ _ _ _ e']
  · exact Submodule.mem_top
  · exact of_tr_mem_ur _ _ _ _ _ _ _ hv'

theorem selC_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  intro D N X bkP i s Λ _ _ Λ' _ _ φ κ κ' hκ Y _ _ _ _ _ hY
  refine ⟨repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ, fun Q f => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ hz⟩
  · rintro ⟨z, rfl, hz⟩
    refine ⟨back _ _ (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      of_trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ ?_⟩
    have e := tr_back (φ : Λ →+* Λ') (vec_smul φ hY) (repOn (Tgl i s) κ Y) (repOn (Tgl i s) κ' Y)
      (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z
    exact e ▸ hz

end GlobalTheory.NewPrime.ScalarChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.SFil

def texp {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (x : R) :
    Matrix (Fin d) (Fin d) R :=
  ∑ i ∈ Finset.range d, (q ((i.factorial : ℚ)⁻¹) * x ^ i) • N ^ i

theorem map_sum_smul_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (a : ℕ → R) :
    (∑ i ∈ Finset.range d, a i • N ^ i).map f = ∑ i ∈ Finset.range d, f (a i) • (N.map f) ^ i := by
  change f.mapMatrix _ = ∑ i ∈ Finset.range d, f (a i) • (f.mapMatrix N) ^ i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow]
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem texp_map {R R' : Type} [CommRing R] [CommRing R'] (q : ℚ →+* R) (q' : ℚ →+* R') (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (x : R) : (texp q N x).map f = texp q' (N.map f) (f x) := by
  have e : q' = f.comp q := Subsingleton.elim _ _
  unfold texp
  rw [map_sum_smul_pow, e]
  simp only [map_mul, map_pow, RingHom.comp_apply]

theorem texp_add {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (hN : N ^ d = 0)
    (x y : R) : texp q N x * texp q N y = texp q N (x + y) := by
  letI : Algebra ℚ R := q.toAlgebra
  have h : ∀ z : R, (z • N) ^ d = 0 := fun z => by rw [smul_pow, hN, smul_zero]
  have e : ∀ z : R, texp q N z = IsNilpotent.exp (z • N) := fun z => by
    rw [IsNilpotent.exp_eq_sum (h z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, mul_smul]
    exact algebraMap_smul R ((i.factorial : ℚ)⁻¹) _
  rw [e, e, e, add_smul, IsNilpotent.exp_add_of_commute _ ⟨d, h x⟩ ⟨d, h y⟩]
  exact ((Commute.refl N).smul_left x).smul_right y

theorem texp_zero {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) :
    texp q N 0 = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold texp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem texp_sub_mem {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (I : Ideal R)
    {x y : R} (h : x - y ∈ I) (i j : Fin d) : (texp q N x - texp q N y) i j ∈ I := by
  unfold texp
  rw [← Finset.sum_sub_distrib, Matrix.sum_apply]
  refine I.sum_mem fun n _ => ?_
  rw [← sub_smul, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact I.mul_mem_right _ (I.mul_mem_left _ (Ideal.mem_of_dvd I (sub_dvd_pow_sub_pow x y n) h))

theorem cleared_map {S R : Type} [CommRing S] [CommRing R] (q : ℚ →+* R) (f : S →+* R) {d : ℕ}
    (N : Matrix (Fin d) (Fin d) S) {l : ℕ} (hl : l ≠ 0) (c e : ℕ) (a : ℕ → S)
    (ha : ∀ i < d, ((i.factorial : S) * (l : S) ^ (c * i)) * a i = (l : S) ^ e) (x : S) :
    (∑ i ∈ Finset.range d, (a i * x ^ i) • N ^ i).map f =
      (l : R) ^ e • texp q (N.map f) (q ((l : ℚ) ^ c)⁻¹ * f x) := by
  rw [map_sum_smul_pow]
  unfold texp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul]
  congr 1
  have h1 := congrArg f (ha i (Finset.mem_range.1 hi))
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 : q ((i.factorial : ℚ)⁻¹) * q ((l : ℚ) ^ c)⁻¹ ^ i * ((i.factorial : R) * (l : R) ^ (c * i)) = 1 := by
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
    have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    rw [← map_natCast q, ← map_natCast q l, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_one q]
    congr 1
    rw [pow_mul, inv_pow]
    field_simp
  rw [map_mul, map_pow, mul_pow, ← h1]
  linear_combination (-(f (a i) * f x ^ i)) * h2

theorem exists_cleared {l : ℕ} [Fact l.Prime] (c d : ℕ) :
    ∃ (e : ℕ) (a : ℕ → ℤ_[l]), ∀ i < d, ((i.factorial : ℤ_[l]) * (l : ℤ_[l]) ^ (c * i)) * a i = (l : ℤ_[l]) ^ e := by
  obtain ⟨e, m, hm, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd d.factorial_ne_zero l (Fact.out : l.Prime).ne_one
  refine ⟨e + c * d, fun i => ecoef l (e + c * d) c i, fun i hi => ?_⟩
  apply Subtype.ext
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  push_cast
  rw [ecoef_val (ecoefQ_norm_le c hm hd hi)]
  unfold ecoefQ
  field_simp

theorem approx {l : ℕ} [Fact l.Prime] {S R : Type} [CommRing S] [IsDomain S] [CharZero S] [CommRing R]
    (z : ℤ_[l] →+* S) (q : ℚ →+* R) (f : S →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (hN : N ^ d = 0)
    (I : Ideal R) (k k' : ℕ) (s : S) (lam : R) (h : f s - (l : R) ^ k' * lam ∈ I) :
    ∃ (e : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) S), Λ * Λ' = (l : S) ^ (2 * e) • (1 : Matrix (Fin d) (Fin d) S) ∧
      ∀ i j, (Λ.map f - (l : R) ^ e • texp q (N.map f) (-(q ((l : ℚ) ^ k)⁻¹ * lam))) i j ∈ I := by
  obtain ⟨e, a, ha⟩ := exists_cleared (l := l) (k + k') d
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ha' : ∀ i < d, ((i.factorial : S) * (l : S) ^ ((k + k') * i)) * z (a i) = (l : S) ^ e := fun i hi => by
    simpa only [map_mul, map_pow, map_natCast] using congrArg z (ha i hi)
  refine ⟨e, ∑ i ∈ Finset.range d, (z (a i) * (-s) ^ i) • N ^ i, ∑ i ∈ Finset.range d, (z (a i) * s ^ i) • N ^ i,
    ?_, fun i j => ?_⟩
  · have hinj := IsFractionRing.injective S (FractionRing S)
    apply Matrix.map_injective hinj
    have hN' : (N.map (algebraMap S (FractionRing S))) ^ d = 0 := by
      change ((algebraMap S (FractionRing S)).mapMatrix N) ^ d = 0
      rw [← map_pow, hN, map_zero]
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha', cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha',
      Matrix.smul_mul, Matrix.mul_smul, texp_add _ _ hN', map_neg, mul_neg, neg_add_cancel, texp_zero, smul_smul,
      ← pow_add, two_mul]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [cleared_map q f N hl _ _ _ ha', ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    refine I.mul_mem_left _ (texp_sub_mem q _ I ?_ i j)
    have h2 : q ((l : ℚ) ^ k)⁻¹ = q ((l : ℚ) ^ (k + k'))⁻¹ * (l : R) ^ k' := by
      have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
      rw [← map_natCast q l, ← map_pow, ← map_mul]
      congr 1
      field_simp
      ring
    have h3 := I.mul_mem_left (-q ((l : ℚ) ^ (k + k'))⁻¹) h
    convert h3 using 1
    rw [h2, map_neg]
    ring

theorem invariant_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF d ρ U k Mn c hMn hU lam hlam happ
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, hDp, -, -⟩ := ActLaws.act_laws l
  let q : ℚ →+* Per.BdRp l := C.o.comp (algebraMap ℚ (Om l))
  let a : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l)
  let w : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a).toRingHom
  refine ⟨texp q (Mn.map w) (-(q ((l : ℚ) ^ k)⁻¹ * lam)), fun g => ?_, fun m => ?_⟩
  · have hN : ((Mn.map w).map a) ^ d = 0 := by
      change (a.mapMatrix (w.mapMatrix Mn)) ^ d = 0
      rw [← map_pow, ← map_pow, hMn, map_zero, map_zero]
    have hNσ : ((Mn.map w).map a).map (Per.σD (g : GQ l)) = (Mn.map w).map a := by
      ext i j
      change Per.σD (g : GQ l) (a (aDp l (wA l bk.a (Mn i j)))) = a (aDp l (wA l bk.a (Mn i j)))
      rw [hD, hDp, bk.gal_w]
    have hq : ∀ x : ℚ, Per.σD (g : GQ l) (a (q x)) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim ((Per.σD (g : GQ l)).comp (a.comp q)) (a.comp q)) x
    have hqB : ∀ x : ℚ, C.ι (C.qB (x : ℚ_[l])) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim (C.ι.comp (C.qB.comp (Rat.castHom ℚ_[l]))) (a.comp q)) x
    have h1 := congrArg (fun M => Matrix.map M C.ι) (hU g)
    simp only [Matrix.map_mul] at h1
    rw [map_sum_smul_pow] at h1
    have e1 : ((ρ g).map (Per.zB l)).map C.ι = (ρ g).map (Per.zD l) := by
      ext i j
      change C.ι (Per.zB l (ρ g i j)) = Per.zD l (ρ g i j)
      rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]
    have e2 : (U.map (Per.σB (g : GQ l))).map C.ι = (U.map C.ι).map (Per.σD (g : GQ l)) := by
      ext i j
      exact ULaws.iota_sigma C _ _
    have e3 : (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)).map C.ι = (Mn.map w).map a := by
      ext i j
      exact ULaws.iota_aB C _
    have e4 : ∑ i ∈ Finset.range d, C.ι (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l (c g) * C.tB) ^ i) • ((Mn.map w).map a) ^ i =
        texp (a.comp q) ((Mn.map w).map a) (a (q ((l : ℚ) ^ k)⁻¹) * a (aDp l (Per.zA l (c g)) * C.j C.t)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have e5 : (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) =
          (((i.factorial : ℚ)⁻¹ * ((l : ℚ) ^ k)⁻¹ ^ i : ℚ) : ℚ_[l]) := by
        push_cast
        rw [mul_inv, pow_mul, inv_pow]
      have e6 : C.ι (Per.zB l (c g)) = a (aDp l (Per.zA l (c g))) := by
        rw [← ULaws.u_padicInt C, C.ι_u, ← C.o_sec.z]
        rfl
      have e7 : C.ι C.tB = a (C.j C.t) := C.ι_j _
      rw [map_mul C.ι, e5, hqB, map_pow C.ι, map_mul C.ι, e6, e7]
      simp only [map_mul, map_pow, RingHom.comp_apply, mul_pow]
      ring
    rw [e1, e2, e3, e4] at h1
    change _ * (U.map C.ι * Matrix.map _ a).map _ = U.map C.ι * Matrix.map _ a
    rw [texp_map q (a.comp q) a, Matrix.map_mul, texp_map (a.comp q) (a.comp q), hNσ, ← Matrix.mul_assoc, h1,
      Matrix.mul_assoc, texp_add _ _ hN]
    congr 2
    have e8 : Per.σD (g : GQ l) (a lam) = a lam + a (aDp l (Per.zA l (c g)) * C.j C.t) :=
      (hD _ lam).trans ((congrArg a (hlam g)).trans (map_add a _ _))
    rw [map_neg a, map_mul a (q _), map_neg, map_mul (Per.σD (g : GQ l)), hq, e8]
    ring
  · obtain ⟨k', s, -, hs⟩ := happ m
    haveI : CharZero bk.S := RingHom.charZero ((Per.θD l).comp ((aDp l).comp bk.ev))
    have hN : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)) ^ d = 0 := by
      change ((PowerSeries.C : Wq l bk.a →+* bk.S).mapMatrix Mn) ^ d = 0
      rw [← map_pow, hMn, map_zero]
    have e1 : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)).map ((aDp l).comp bk.ev) = Mn.map w := by
      ext i j
      exact congrArg (aDp l) (bk.ev_C _)
    have := approx ((PowerSeries.C : Wq l bk.a →+* bk.S).comp (algebraMap ℤ_[l] (Wq l bk.a))) q
      ((aDp l).comp bk.ev) _ hN (Per.FilP l m) k k' s lam hs
    rwa [e1] at this

end GlobalTheory.SstPer.SFil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocyclePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem sum_inv_eq_zero_of_unramified_cocycle_pow : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (ζ : Ω), 0 < n → IsPrimitiveRoot ζ (l ^ n) → ∃ inv : InvFam F Ω l n, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l n), (∀ g h : G F Ω, ∀ u ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ u' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * u, h * u') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l n (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ n ζ hn hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l n hn ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := n) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l n g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatioStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_kap_and_lam0_hasInf : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → (∀ g, 1 ≤ Z.kap j a s g) ∧ GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  first | exact @GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | exact GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio | (intros; apply GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlace
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.AllLaws

theorem laws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  intro D HW F l _ K s LL h W E
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact ⟨GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity D HW l K s LL h, GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant D HW F l K s LL h,
    GlobalTheory.TrivCrys.isCrys_lat_of_trivial W.one W.one_triv⟩

end GlobalTheory.NL.AllLaws
end

