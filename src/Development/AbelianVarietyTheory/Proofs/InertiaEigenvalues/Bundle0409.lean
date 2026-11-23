module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.QuoFree

theorem finite_of_killed {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] [hM : Module.Finite A M] (q : A)
    (hq : ∀ m : M, q • m = 0) (F : Finset A)
    (hF : ∀ a : A, ∃ c, a - q * c ∈ Submodule.span R (F : Set A)) : Module.Finite R M := by
  obtain ⟨Gs, hG⟩ := hM.fg_top
  set P := Submodule.span R (Set.image2 (· • ·) (F : Set A) (Gs : Set M)) with hPdef
  have key : ∀ b ∈ Submodule.span R (F : Set A), ∀ g ∈ Gs, b • g ∈ P := by
    intro b hb g hg
    induction hb using Submodule.span_induction with
    | mem f hf => exact Submodule.subset_span ⟨f, hf, g, hg, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_assoc]; exact Submodule.smul_mem _ r hx
  have hsplit : ∀ (a : A) (g : M), g ∈ Gs → a • g ∈ P := by
    intro a g hg
    obtain ⟨c, hc⟩ := hF a
    have : a • g = (a - q * c) • g := by
      rw [sub_smul, mul_comm, mul_smul, hq, smul_zero, sub_zero]
    rw [this]
    exact key _ hc g hg
  let P' : Submodule A M :=
    { carrier := P
      add_mem' := fun ha hb => P.add_mem ha hb
      zero_mem' := P.zero_mem
      smul_mem' := by
        intro a m hm
        induction hm using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨f, hf, g, hg, rfl⟩ := hx
          change a • (f • g) ∈ P
          rw [← mul_smul]
          exact hsplit _ g hg
        | zero => simp
        | add x y _ _ hx hy => rw [smul_add]; exact P.add_mem hx hy
        | smul r x _ hx => rw [smul_comm]; exact P.smul_mem r hx }
  have htop : P = ⊤ := by
    refine eq_top_iff.2 fun m _ => ?_
    have hm : m ∈ Submodule.span A (Gs : Set M) := by rw [hG]; trivial
    have hle : Submodule.span A (Gs : Set M) ≤ P' := Submodule.span_le.2 fun g hg => by
      have := hsplit 1 g hg
      rwa [one_smul] at this
    exact hle hm
  refine ⟨?_⟩
  rw [← htop]
  exact Submodule.fg_span (Set.Finite.image2 _ F.finite_toSet Gs.finite_toSet)

theorem coe_poly_eq_sum {O : Type} [CommRing O] (D : ℕ) (r : Polynomial O) (hr : r.degree < D) :
    (r : PowerSeries O) = ∑ k ∈ Finset.range D, r.coeff k • (PowerSeries.X : PowerSeries O) ^ k := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.coeff_coe, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hm
  · rfl
  · exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast not_lt.1 hm))

theorem div_letters {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (n : ℕ) [NeZero n] (g : PowerSeries O)
    (hg : g.map (IsLocalRing.residue O) ≠ 0) :
    ∃ F : Finset (LetA O n), ∀ a : LetA O n, ∃ c,
      a - (fun _ => g) * c ∈ Submodule.span O (F : Set (LetA O n)) := by
  classical
  have H : g.IsWeierstrassDivisor := PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hg
  set D := (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat
  refine ⟨(Finset.univ ×ˢ Finset.range D).image
    (fun p : ZMod n × ℕ => (Pi.single p.1 ((PowerSeries.X : PowerSeries O) ^ p.2) : LetA O n)), ?_⟩
  intro a
  refine ⟨fun i => H.div (a i), ?_⟩
  have hdecomp : a - (fun _ => g) * (fun i => H.div (a i)) =
      ∑ i : ZMod n, ∑ k ∈ Finset.range D,
        (H.mod (a i)).coeff k • (Pi.single i ((PowerSeries.X : PowerSeries O) ^ k) : LetA O n) := by
    funext j
    have hd := H.isWeierstrassDivisionAt_div_mod (a j)
    rw [Pi.sub_apply, Pi.mul_apply]
    rw [show a j - g * H.div (a j) = ((H.mod (a j) : Polynomial O) : PowerSeries O) from
      sub_eq_iff_eq_add'.2 hd.eq_mul_add]
    rw [coe_poly_eq_sum D _ hd.degree_lt, Finset.sum_apply,
      Finset.sum_eq_single j]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_same]
    · intro b _ hb
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_univ, Set.mem_image, Set.mem_prod,
    Set.mem_univ, true_and, Finset.mem_coe, Finset.mem_range]
  exact ⟨(i, k), Finset.mem_range.1 hk, rfl⟩

theorem dvd_pow_of_nonunit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {c p : O} (hc : c ≠ 0) (hp : ¬ IsUnit p) : ∃ k : ℕ, c ∣ p ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : ϖ ∣ p := by
    have : p ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hp
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  exact ⟨k, (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd h1 k)⟩

theorem QQ_pow_map_ne {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (s : ℕ) (hs : 1 ≤ s) (y : ℕ) :
    (GlobalTheory.Cyc.QQ l O s ^ y).map (IsLocalRing.residue O) ≠ 0 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Cyc.XX_QQ_properties l O s hs).2.2.2.1
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hl)
  have hl1 : ((l : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hl0, map_zero]
  rw [map_pow, hb, map_add (f := _), map_mul, map_natCast, map_pow, PowerSeries.map_X, hl1, zero_mul, add_zero,
    ← pow_mul]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

end GlobalTheory.NL.QuoFree

namespace GlobalTheory.NL.QuoFree

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem torsionFree_quo [IsDomain O] [IsDiscreteValuationRing O] (hp : ¬ IsUnit ((PD.p : ℕ) : O))
    (T : LocLat G Qp LL O) (hsat : wachSaturated W T) (S : Submodule (LetA O n) (W.DD T)) :
    Module.IsTorsionFree O (quo W T S (W.N T)) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c z hz => ?_
  rcases eq_or_ne c 0 with hc | hc
  · exact Or.inl hc
  right
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower] at hz ⊢
  obtain ⟨k, d, hd⟩ := dvd_pow_of_nonunit hc hp
  refine hsat (x : W.DD T) ⟨k, ?_⟩
  rw [GlobalTheory.NL.Isog.pow_smul_eq, hd, mul_comm, mul_smul, ← algebraMap_smul (LetA O n) d]
  exact (W.N T).smul_mem _ hz

theorem finite_quo (T : LocLat G Qp LL O) (q : LetA O n)
    (hq : IsUnit (algebraMap (LetA O n) W.EE q)) (F : Finset (LetA O n))
    (hF : ∀ a : LetA O n, ∃ c, a - q * c ∈ Submodule.span O (F : Set (LetA O n))) :
    Module.Finite O (quo W T (invN W T q) (W.N T)) := by
  set u : W.EE := ↑(hq.unit⁻¹)
  have hinv : ∀ x : W.DD T, q • (u • x) = x := by
    intro x
    rw [← algebraMap_smul W.EE q (u • x), smul_smul]
    have : algebraMap (LetA O n) W.EE q * u = 1 := hq.mul_val_inv
    rw [this, one_smul]
  let φu : W.DD T →ₗ[LetA O n] W.DD T := (LinearMap.lsmul W.EE (W.DD T) u).restrictScalars (LetA O n)
  have hS : invN W T q = (W.N T).map φu := by
    ext z
    constructor
    · intro hz
      refine ⟨q • z, hz, ?_⟩
      change u • (q • z) = z
      rw [← algebraMap_smul W.EE q z, smul_smul, mul_comm, hq.mul_val_inv, one_smul]
    · rintro ⟨x, hx, rfl⟩
      change q • (u • x) ∈ W.N T
      rw [hinv]
      exact hx
  haveI : Module.Finite (LetA O n) ↥(invN W T q) := by
    rw [hS]
    exact Module.Finite.iff_fg.2 ((W.N_fg T).map φu)
  haveI : Module.Finite (LetA O n) (quo W T (invN W T q) (W.N T)) :=
    Module.Finite.quotient (LetA O n) _
  refine finite_of_killed q (fun m => ?_) F hF
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower]
  exact x.2

end Generic


set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem quo_free_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  intro D HW F l _ K s LL h W T hT y
  obtain ⟨hdvr, hcomp, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have := hdvr
  have := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hQ : ∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s := by
    obtain ⟨_, _, _, _, _, hQ, _⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
    exact hQ
  have hQy : W.Q ^ y = fun _ => GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y := by
    funext i
    rw [Pi.pow_apply, hQ]
  have hunit : IsUnit (algebraMap (AA K LL) W.EE (W.Q ^ y)) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    rw [map_pow]
    exact this.pow y
  have hp : ¬ IsUnit ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) := by
    rw [(D.loc l).PD_p K]
    exact hl
  have hsat := (GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h).1 T hT
  have := hcomp
  obtain ⟨Fs, hFs⟩ := div_letters (Module.finrank ℚ_[l] ↥(K0 K)) (GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y)
    (QQ_pow_map_ne hl s h.1 y)
  have hfin : Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) :=
    finite_quo W T (W.Q ^ y) hunit Fs (by rw [hQy]; exact hFs)
  have := torsionFree_quo W hp T hsat (invN W T (W.Q ^ y))
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GlobalTheory.NL.QuoFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.EtMem

section Lin

variable {E S D M : Type} [CommRing E] [CommRing S] [AddCommGroup D] [Module E D] [AddCommGroup M] [Module S M]

theorem exists_basis [Nontrivial S] [Module.Free S M] [Module.Finite S M] {r : ℕ} (io : E → S) (j : D →+ M)
    (hj : ∀ e x, j (e • x) = io e • j x) (hsp : Submodule.span S (Set.range j) = ⊤)
    (b : Module.Basis (Fin r) E D) (hr : Module.finrank S M = r) :
    ∃ e : Module.Basis (Fin r) S M, ∀ i, e i = j (b i) := by
  have h : ⊤ ≤ Submodule.span S (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hj]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank _ h (by simp [hr]), fun i => by simp⟩

theorem repr_semi {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (m : M) (i : Fin r) :
    e.repr (Φ m) i = ∑ k, e.repr (Φ (e k)) i * φ (e.repr m k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← e.sum_repr m, map_sum, map_sum]
  simp [hΦ, Finsupp.finsetSum_apply, mul_comm]

theorem isUnit_det {r : ℕ} (e : Module.Basis (Fin r) S M) (φ : S → S) (Φ : M →+ M)
    (hΦ : ∀ c m, Φ (c • m) = φ c • Φ m) (hsp : Submodule.span S {m | Φ m = m} = ⊤) :
    IsUnit (Matrix.of fun i k => e.repr (Φ (e k)) i).det := by
  have h : ∀ m : M, ∃ w : Fin r → S, ∀ i, e.repr m i = ∑ k, e.repr (Φ (e k)) i * w k := by
    intro m
    have hm : m ∈ Submodule.span S {m | Φ m = m} := hsp ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine ⟨fun k => φ (e.repr x k), fun i => ?_⟩
      rw [← repr_semi e φ Φ hΦ, show Φ x = x from hx]
    | zero => exact ⟨0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨w, hw⟩ := hy
      exact ⟨u + w, fun i => by simp [hu, hw, mul_add, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu⟩ := hx
      exact ⟨c • u, fun i => by simp [hu, Finset.mul_sum, mul_left_comm]⟩
  choose w hw using h
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k j => w (e j) k) ?_
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← hw, e.repr_self, Matrix.one_apply, Finsupp.single_apply]
  simp [eq_comm]

end Lin

section Ten

variable {O S N : Type} [CommRing O] [CommRing S] [Algebra O S] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : S →ₐ[O] S) (g : N →ₗ[O] N) (c : S) (m : S ⊗[O] N) :
    TensorProduct.map f.toLinearMap g (c • m) = f c • TensorProduct.map f.toLinearMap g m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem map_mulLeft (c : S) (m : S ⊗[O] N) :
    TensorProduct.map (LinearMap.mulLeft O c) (LinearMap.id : N →ₗ[O] N) m = c • m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem span_fixed (f : S →ₐ[O] S) :
    Submodule.span S {m : S ⊗[O] N | TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) m = m} = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have : a ⊗ₜ[O] t = a • ((1 : S) ⊗ₜ[O] t) := by simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Ten

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem res_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G) (hg : (PD.χ g : Qp) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one Γ.χΓ]
  apply Units.ext
  apply hO
  rw [Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]

theorem mem_range (E : WEt I) (T : LocLat G Qp LL O) (H : G → Prop) (hH : ∀ g, H g → Γ.resΓ g = 1)
    (hu : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) (q : ℕ) (x : Fin q → TW RW T)
    (A : Matrix (Fin q) (Fin q) R.EE)
    (hrat : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) RW), IsUnit F →
      (∀ i j g, H g → gR g (U i j) = U i j) → F.map I.ioE * U.map φR = U * A.map I.ioE →
      ∀ i j, U i j ∈ Set.range I.ioE)
    (hx : ∀ g, H g → ∀ i, TWact (gR g) T g (x i) = x i)
    (hφ : ∀ j, TWmap φR T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft O (I.ioE (A i j) : RW))
      (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (x i)) :
    ∀ i, x i ∈ Set.range (E.jD T) := by
  intro i₀
  rcases subsingleton_or_nontrivial RW with hS | hS
  · haveI : Subsingleton (TW RW T) := Module.subsingleton RW _
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Nontrivial O := (algebraMap O RW).domain_nontrivial
  haveI : Nontrivial R.EE := I.ioE.toRingHom.domain_nontrivial
  haveI : Module.Free O ↥T.L.T := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free R.EE (E.DD T) := (E.DD_free T).1
  have hrk : Module.finrank RW (TW RW T) = Module.finrank O ↥T.L.T := Module.finrank_baseChange
  rcases Nat.eq_zero_or_pos (Module.finrank O ↥T.L.T) with h0 | h0
  · haveI : Subsingleton (TW RW T) := (Module.finrank_eq_zero_iff_of_free RW _).1 (hrk.trans h0)
    exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Module.Finite R.EE (E.DD T) := Module.finite_of_finrank_pos ((E.DD_free T).2 ▸ h0)
  let b := Module.finBasisOfFinrankEq R.EE (E.DD T) (E.DD_free T).2
  obtain ⟨e, he⟩ := exists_basis I.ioE (E.jD T).toAddMonoidHom (E.jD_smul T) (E.jD_span T) b hrk
  have he' : ∀ i, e i = E.jD T (b i) := he
  have hrep : ∀ (d : E.DD T) i, e.repr (E.jD T d) i = I.ioE (b.repr d i) := by
    intro d i
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr d, map_sum]
    simp only [E.jD_smul, ← he']
    rw [e.repr_sum_self]
  have hsφ : ∀ (c : RW) (m : TW RW T), (TWmap φR T).toAddMonoidHom (c • m) =
      φR c • (TWmap φR T).toAddMonoidHom m := fun c m => map_smul_semi φR _ c m
  let F : Matrix (Fin (Module.finrank O ↥T.L.T)) (Fin (Module.finrank O ↥T.L.T)) R.EE :=
    Matrix.of fun i k => b.repr (E.φD T (b k)) i
  have hF : F.map I.ioE = Matrix.of fun i k => e.repr ((TWmap φR T).toAddMonoidHom (e k)) i := by
    ext i k
    simp only [F, Matrix.map_apply, Matrix.of_apply, LinearMap.toAddMonoidHom_coe]
    rw [he', ← E.jD_φ, hrep]
  have hFu : IsUnit F := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply hu
    have h1 := isUnit_det e φR (TWmap φR T).toAddMonoidHom hsφ (span_fixed φR)
    rw [← hF] at h1
    rw [AlgHom.map_det]
    exact h1
  have hU := hrat _ F (Matrix.of fun k j => e.repr (x j) k) hFu ?_ ?_
  · choose u hu' using hU
    refine ⟨∑ k, u k i₀ • b k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [E.jD_smul, ← he', hu', Matrix.of_apply]
    exact e.sum_repr _
  · intro i j g hg
    have hs : ∀ (c : RW) (m : TW RW T), (TWact (gR g) T g).toAddMonoidHom (c • m) =
      gR g c • (TWact (gR g) T g).toAddMonoidHom m := fun c m => map_smul_semi (gR g) _ c m
    have h1 := repr_semi e (gR g) (TWact (gR g) T g).toAddMonoidHom hs (x j) i
    have h2 : ∀ k, TWact (gR g) T g (e k) = e k := fun k => by
      rw [he', ← E.jD_act, hH g hg, E.γD_one]
    simp only [LinearMap.toAddMonoidHom_coe, hx g hg, h2, e.repr_self, Finsupp.single_apply] at h1
    simp only [Matrix.of_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h1
    simpa using h1.symm
  · rw [hF]
    ext i j
    have h1 := repr_semi e φR (TWmap φR T).toAddMonoidHom hsφ (x j) i
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [← h1, LinearMap.toAddMonoidHom_coe, hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mulLeft, map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Generic


set_option maxHeartbeats 1000000 in
theorem fixed_mem_range : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (q : ℕ) (x : Fin q → TW (RW LL) T) (A : Matrix (Fin q) (Fin q) R.EE), IsUnit A → (∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → ∀ i, TWact (AI.gRW LL (g : GQ l)) T g (x i) = x i) → (∀ j, TWmap (φRW LL) T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (I.ioE (A i j) : RW LL)) (LinearMap.id : ↥T.L.T →ₗ[↥(OL LL)] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T) := by
  intro l _ P AI K s LL hG Γ R I hI E T q x A hA hx hφ
  have h1 : ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → Γ.resΓ g = 1 := fun g hg =>
    res_eq_one Subtype.val_injective g ((P.PD_χ K g).trans (congrArg Units.val hg))
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 : ∀ (p : ℕ) (F : Matrix (Fin p) (Fin p) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit F →
      (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (U i j) = U i j) →
      F.map I.ioE * U.map (φRW LL) = U * A.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE :=
    fun p F U hF hU hE => GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach l P AI K s LL hG Γ R I hI p q F A 0 U hF hA
      (fun i j g hg h1 => hU i j ⟨g, hg⟩ h1)
      (by simpa only [Matrix.map_zero, map_zero, add_zero] using hE)
  exact mem_range E T (fun g => P.χQ (g : GQ l) = 1) h1 (GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hI).2.1 q x A
    h2 hx hφ

end GlobalTheory.HWL.EtMem
end
end

