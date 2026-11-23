module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLattic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenFiniteOfNoTower
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.PMon.Ram

theorem senFinite_of_noTower (hNT : NoTower) : SenFinite := by
  intro l _ n _ _ K ρ hc M hM
  obtain ⟨N, hN, hanti, hopen, hpow, hroot, hker⟩ := _root_.GlobalTheory.congrFiltration l n K ρ hc
  have hdet := _root_.GlobalTheory.congrFiltration_detectingCharacters_coboundary l n K ρ M hM N hN
  obtain ⟨k, hk⟩ := hNT l K N hanti hopen hpow hroot hdet
  refine _root_.GlobalTheory.GK.finite_image_of_trivial_on_open l K (GL n ℚ_[l]) ρ (IK K) (N k) (hopen k) ?_
  intro g hgI hgN
  exact hker g (fun j => hk j ⟨hgI, hgN⟩)

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRangeMap
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EtaleBasis

section Generic

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem repr_of_fixed (e : Module.Basis (Fin r) R M) (τ : R →+* R) (A : M →+ M)
    (hA : ∀ c x, A (c • x) = τ c • A x) (he : ∀ i, A (e i) = e i) (x : M) (i : Fin r) :
    e.repr (A x) i = τ (e.repr x i) := by
  have h : A x = ∑ k, τ (e.repr x k) • e k := by
    conv_lhs => rw [← e.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hA, he]
  rw [h, e.repr_sum_self]

theorem isUnit_matrix (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (hs : Submodule.span R (Set.range Φ) = ⊤) :
    IsUnit (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hle : Submodule.span R (Set.range Φ) ≤ Submodule.span R (Set.range fun j => Φ (e j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hΦ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro y
  have hy : e.equivFun.symm y ∈ Submodule.span R (Set.range fun j => Φ (e j)) :=
    hle (hs ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨c, funext fun i => ?_⟩
  have h1 : e.equivFun (e.equivFun.symm y) i = y i := by rw [LinearEquiv.apply_symm_apply]
  rw [← h1, ← hc]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem change_basis (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (V F₁ : Matrix (Fin r) (Fin r) R) (hV : IsUnit V)
    (h : (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) * V.map σ = V * F₁) :
    ∃ e' : Module.Basis (Fin r) R M, (∀ j, e' j = ∑ i, V i j • e i) ∧
      ∀ i j, e'.repr (Φ (e' j)) i = F₁ i j := by
  obtain ⟨u, rfl⟩ := hV
  let L : M ≃ₗ[R] M := Matrix.toLinOfInv e e u.mul_inv u.inv_mul
  have hL : ∀ j, (e.map L) j = ∑ i, (u : Matrix (Fin r) (Fin r) R) i j • e i := by
    intro j
    simp [L, Matrix.toLinOfInv, Matrix.toLin_self]
  refine ⟨e.map L, hL, fun i j => ?_⟩
  have key : Φ ((e.map L) j) = ∑ k, F₁ k j • (e.map L) k := by
    apply e.repr.injective
    ext m
    have hm := congrFun (congrFun h m) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply] at hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hL, map_sum, hΦ, map_smul, smul_eq_mul, Finsupp.single_apply]
    simpa only [mul_comm] using hm
  rw [key, Module.Basis.repr_sum_self]

end Generic

section Tensor

variable {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : R →ₐ[O] R) (a : N →ₗ[O] N) (c : R) (x : R ⊗[O] N) :
    TensorProduct.map f.toLinearMap a (c • x) = f c • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul b t => simp [TensorProduct.smul_tmul']

theorem span_range_map (f : R →ₐ[O] R) :
    Submodule.span R (Set.range (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b t =>
    have : b ⊗ₜ[O] t = b • TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) ((1 : R) ⊗ₜ[O] t) := by
      simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem map_comm (f g : R →ₐ[O] R) (h : ∀ c, f (g c) = g (f c)) (a : N →ₗ[O] N) (x : R ⊗[O] N) :
    TensorProduct.map g.toLinearMap a (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) x) =
      TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) (TensorProduct.map g.toLinearMap a x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t => simp [h]

theorem descend {r : ℕ} {ι : Type} (φ : R →ₐ[O] R) (g : ι → (R →ₐ[O] R)) (a : ι → (N →ₗ[O] N))
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (R ⊗[O] N))
    (he : ∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (R ⊗[O] N),
      (∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e' i) = e' i) ∧
      ∀ i j, e'.repr (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N) (e' j)) i ∈ S := by
  let Φ : R ⊗[O] N →+ R ⊗[O] N :=
    (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N)).toAddMonoidHom
  have hΦ : ∀ (c : R) x, Φ (c • x) = (φ : R →+* R) c • Φ x := map_smul_semi φ _
  obtain ⟨V, F₁, hV, hVg, hS, hE⟩ := dec _ (isUnit_matrix e φ Φ hΦ (span_range_map φ)) (by
    intro i j s
    have h1 := repr_of_fixed e (g s : R →+* R)
      (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (map_smul_semi (g s) _) (he s) (Φ (e j)) i
    have h2 : (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (Φ (e j)) = Φ (e j) := by
      have := map_comm φ (g s) (hc s) (a s) (e j)
      rw [he] at this
      exact this
    rw [h2] at h1
    exact h1.symm)
  obtain ⟨e', h1, h2⟩ := change_basis e φ Φ hΦ V F₁ hV hE
  refine ⟨e', fun s j => ?_, fun i j => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul_semi, hVg, he]
  · have := hS i j
    rw [← h2] at this
    exact this

end Tensor

theorem descend_lat {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (T : LocLat G Qp LL O) {r : ℕ} (φ : R →ₐ[O] R) (g : G → (R →ₐ[O] R)) (H : G → Prop)
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, H s → g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, H s → g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (TW R T)) (he : ∀ s, H s → ∀ i, TWact (g s) T s (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (TW R T), (∀ s, H s → ∀ i, TWact (g s) T s (e' i) = e' i) ∧
      ∀ i j, e'.repr (TWmap φ T (e' j)) i ∈ S := by
  obtain ⟨e', h1, h2⟩ := descend (ι := {s : G // H s}) φ (fun s => g s.1) (fun s => T.actT s.1)
    (fun s c => hc s.1 c) S
    (fun F hU hfix => by
      obtain ⟨V, F₁, hV, hVf, hS, hE⟩ := dec F hU (fun i j s hs => hfix i j ⟨s, hs⟩)
      exact ⟨V, F₁, hV, fun i j s => hVf i j s.1 s.2, hS, hE⟩)
    e (fun s i => he s.1 s.2 i)
  exact ⟨e', fun s hs i => h1 ⟨s, hs⟩ i, h2⟩

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g : W →ₐ[Z] W) (h : ∀ w, f (g w) = g (f w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) g (Algebra.TensorProduct.map (AlgHom.id O O) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w => simp [h]

theorem frob_comm_gal {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l)
    (x : RW LL) : φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem fixH_iff {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l}
    (x : RW LL) : FixH AI K x ↔ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) x = x := by
  unfold FixH
  constructor
  · intro h g hχ
    exact h g.1 g.2 hχ
  · intro h g hg hχ
    have h1 := h ⟨g, hg⟩
    dsimp only at h1
    exact h1 hχ

theorem decomplete {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hG : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (hI : IoW I) (r : ℕ)
    (F : Matrix (Fin r) (Fin r) (RW LL)) (hU : IsUnit F)
    (hfix : ∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (F i j) = F i j) :
    ∃ V F₁ : Matrix (Fin r) (Fin r) (RW LL),
      IsUnit V ∧ (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (V i j) = V i j) ∧
      (∀ i j, F₁ i j ∈ Set.range I.ioE) ∧ F * V.map (φRW LL) = V * F₁ := by
  have h0 : ∀ i j, FixH AI K (F i j) := fun i j => (fixH_iff AI K _).mpr (hfix i j)
  have h1 := _root_.GlobalTheory.HWL.MatDecompl.decompletion l P AI K s LL hG Γ R I hI r F hU h0
  obtain ⟨V, F', hV, hVf, hE⟩ := h1
  refine ⟨V, F'.map I.ioE, hV, fun i j => (fixH_iff AI K _).mp (hVf i j), ?_, hE⟩
  intro i j
  rw [Matrix.map_apply]
  exact Set.mem_range_self _

theorem exists_etBasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e := by
  intro l _ P AI hF K s LL hG Γ R I hI T
  obtain ⟨e, he⟩ := _root_.GlobalTheory.HWL.FixedBasis.main l P AI hF K LL T
  unfold EtBasis FixBasis
  unfold FixBasis at he
  exact descend_lat T (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) (fun g => P.χQ (g : GQ l) = 1)
    (fun g c => frob_comm_gal AI LL (g : GQ l) c) (Set.range I.ioE)
    (decomplete AI K s LL hG Γ R I hI _) e he

end GlobalTheory.EtaleBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.X_pow_natDegree_mem {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X] at h
  have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i ∈
      Ideal.span {(l : bk.S)} := by
    refine Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    rw [hc, map_mul, map_natCast, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [BK.E, h]; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hs)


set_option maxHeartbeats 1000000 in
theorem BK.hom_eq_of_X_C {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B)
    (hX : BK.hf f X = BK.hf g X) (hC : ∀ w, BK.hf f (C w) = BK.hf g (C w)) : f = g := by
  have hpoly : ∀ p : Polynomial (Wq l bk.a), BK.hf f (p : bk.S) = BK.hf g (p : bk.S) := by
    have e : (BK.hf f).comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
        (BK.hf g).comp Polynomial.coeToPowerSeries.ringHom :=
      Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
    exact fun p => RingHom.congr_fun e p
  have hle : Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} ≤
      (Ideal.span {(l : B.A)} ⊔ B.I).comap (BK.hf f) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_sup_right (f.f_I _ (Ideal.mem_span_singleton_self _))
  have hXe : BK.hf f X ^ bk.Ep.natDegree ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
    rw [← map_pow]; exact hle bk.X_pow_natDegree_mem
  refine Hom.ext' (RingHom.ext fun (s : bk.S) => ?_)
  show BK.hf f s = BK.hf g s
  haveI : IsAdicComplete (Ideal.span {(l : B.A)} ⊔ B.I) B.A := B.complete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : B.A)} ⊔ B.I) B.A) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ : (X : bk.S) ^ (bk.Ep.natDegree * n) ∣ s - (trunc (bk.Ep.natDegree * n) s : bk.S) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, coeff_trunc, hm]
  have e : s = (trunc (bk.Ep.natDegree * n) s : bk.S) + X ^ (bk.Ep.natDegree * n) * r := by
    rw [← hr]; ring
  have hd : BK.hf f s - BK.hf g s = BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) := by
    rw [e]
    simp only [map_add (f := _), map_mul, map_pow]
    rw [hpoly (trunc (bk.Ep.natDegree * n) s), ← hX]; ring
  have h2 : BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) ∈
      (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by
    rw [pow_mul]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXe n)
  have h3 : BK.hf f s - BK.hf g s ∈ (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by rw [hd]; exact h2
  rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact h3

theorem BK.galHom_comp_ι_of_fixFlat {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (hg : bk.FixFlat g) :
    (ainfHom K g).comp bk.ι = bk.ι := by
  refine BK.hom_eq_of_X_C bk _ _ ?_ ?_
  · change Per.σA (g : GQ l) (bk.ev X) = bk.ev X
    rw [bk.ev_X]
    exact (GlobalTheory.RingIface.sigA_teich l _ _).trans (congrArg _ hg)
  · intro w
    change Per.σA (g : GQ l) (bk.ev (C w)) = bk.ev (C w)
    rw [bk.ev_C, bk.gal_w]

theorem MReal.gal_of_fixFlat {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {T : Matrix (Fin d) (Fin d) (WCb l)} (h : MReal S ρ T)
    (g : ↥(GK K)) (hg : bk.FixFlat g) : zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
  have e := h.gal g
  rw [BK.galHom_comp_ι_of_fixFlat bk g hg, S.ε_refl] at e
  exact e.trans ((congrArg (T * ·) (Matrix.map_one (inclW l) (map_zero _) (map_one _))).trans (Matrix.mul_one T))

theorem MReal.exists_fixed_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧
      (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧
      bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨u, hu⟩ := hT'.unit
  have cancel : ∀ M N : Matrix (Fin d') (Fin d) (WCb l), T' * M = T' * N → M = N := by
    intro M N h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * T) with hXm
  have hX : T' * Xm = zW f * T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨Xm, hX, fun g hg => ?_, ?_⟩
  · let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * T'.map G = T' := hT'.gal_of_fixFlat g hg
    have a2 : zW (ρ g) * T.map G = T := hT.gal_of_fixFlat g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc T' * Xm.map G = zW (ρ' g) * (T'.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = T' * Xm := by rw [a2, hX]
  · let F : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map F = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ S.a • T.map F = T * S.A.map bk.evW := hT.φ
    have b2 : bk.evW bk.E ^ S'.a • T'.map F = T' * S'.A.map bk.evW := hT'.φ
    change bk.evW bk.E ^ S.a • (S'.A.map bk.evW * Xm.map F) = bk.evW bk.E ^ S'.a • (Xm * S.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map F) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleEquivariantMatrixCommute
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem strat_homGal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY g
  let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
  have hG : ∀ z : ℤ_[l], G (algebraMap ℤ_[l] (WCb l) z) = algebraMap ℤ_[l] (WCb l) z :=
    fun z => (galW l (g : GQ l)).commutes z
  have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M := by
    intro m n M; exact Matrix.ext fun i j => hG _
  have hYG : (Y.map bk.evW).map G = (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := by
    exact Matrix.ext fun i j => galW_inclW (g : GQ l) (bk.ev (Y i j))
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  have h1 := congrArg (fun M => M.map G) hY
  simp only [Matrix.map_mul, hzG, hYG] at h1

  have e1 : T' * ((S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) *
      (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) =
      T' * ((Y.map (BK.hf bk.ι)).map (inclW l) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) := by
    have a1 := hT'.gal g
    have a2 := hT.gal g
    have a3 : T'.map (galW l (g : GQ l)) = T'.map G := rfl
    have a4 : T.map (galW l (g : GQ l)) = T.map G := rfl
    have a5 : (Y.map (BK.hf bk.ι)).map (inclW l) = Y.map bk.evW := Matrix.map_map
    rw [a3] at a1
    rw [a4] at a2
    rw [a5]
    calc _ = (T' * (S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) *
          (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := (Matrix.mul_assoc _ _ _).symm
      _ = zW (ρ' g) * (T'.map G * (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) := by
          rw [← a1, Matrix.mul_assoc]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = (T' * Y.map bk.evW) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) := by
          rw [a2, hY, Matrix.mul_assoc]
      _ = _ := Matrix.mul_assoc _ _ _
  obtain ⟨u, hu⟩ := hT'.unit
  rw [← hu] at e1
  have e2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) e1
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e2
  apply Matrix.map_injective (f := inclW l) inclW_injective
  exact (Matrix.map_mul (f := inclW l)).trans (e2.trans (Matrix.map_mul (f := inclW l)).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

theorem strat_of_envCocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  intro l _ K bk En d a b A A' hA ε hφ hε
  have comp_assoc : ∀ {P P' P'' P''' : Obj l ↥(OL K)} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P'),
      (h.comp g).comp f = h.comp (g.comp f) := fun _ _ _ => Hom.ext' rfl
  let c : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Hom En.Q B :=
    fun {B} f g => (En.univ B f g).choose
  have hc : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), (c f g).comp En.inl = f ∧ (c f g).comp En.inr = g :=
    fun {B} f g => (En.univ B f g).choose_spec.1
  have hu : ∀ {B : Obj l ↥(OL K)} (k : Hom En.Q B), c (k.comp En.inl) (k.comp En.inr) = k :=
    fun {B} k => ((En.univ B _ _).choose_spec.2 k ⟨rfl, rfl⟩).symm
  clear_value c
  refine ⟨Strat.mk a b A A' hA (fun f g => ε.map (c f g).f) ?_ ?_ ?_ ?_, rfl, rfl, ?_⟩
  · intro B f
    exact (hε B).1 (c f f) ((hc f f).1.trans (hc f f).2.symm)
  · intro B f g h
    exact (hε B).2 (c f g) (c g h) (c f h) ((hc f g).2.trans (hc g h).1.symm)
      ((hc f g).1.trans (hc f h).1.symm) ((hc g h).2.trans (hc f h).2.symm)
  · intro B B' k f g
    have e : c (k.comp f) (k.comp g) = k.comp (c f g) :=
      (En.univ B' (k.comp f) (k.comp g)).unique (hc _ _)
        ⟨by rw [comp_assoc, (hc f g).1], by rw [comp_assoc, (hc f g).2]⟩
    refine Eq.trans ?_ (congrArg (fun k' : Hom En.Q B' => ε.map k'.f) e).symm
    ext i j
    rfl
  · intro B f g
    have e1 : ∀ x, (c f g).f (BK.hf En.inl x) = BK.hf f x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).1
    have e2 : ∀ x, (c f g).f (BK.hf En.inr x) = BK.hf g x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).2
    have e3 : ∀ x, (c f g).f (En.Q.D.φ x) = B.D.φ ((c f g).f x) := (c f g).f_φ
    ext i j
    have h := congrArg (fun M => (c f g).f (M i j)) hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, map_mul, map_pow, map_sum, Matrix.map_apply,
      e1, e2, e3] at h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] using h
  · intro B k
    exact congrArg (fun k' : Hom En.Q B => ε.map k'.f) (hu k)

end GlobalTheory.BSP
end
end

