module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverBridge

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem galF_val {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (z : Fq l a) :
    Per.σF k (Fq.val l a z) = Fq.val l a z ^ l ^ s := by
  obtain ⟨z₀, ω, hω, hz, h⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hω' : k ω = ω ^ l ^ s := hk ω (by
    rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
  have hd : ¬ l ∣ l ^ a - 1 := fun h => hl.out.not_dvd_one
    ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne a))).1 h)
  have h2 : Per.σF k (Fq.val l a z₀) = Fq.val l a z₀ ^ l ^ s := by
    refine GlobalTheory.UnramIdem.tilt_pow (k := l ^ s) hd dvd_rfl hz fun n => ?_
    obtain ⟨y, y1, y2, y3⟩ := hz n
    refine ⟨Per.σO k y, ?_, by rw [← map_pow, y2, map_one], ?_⟩
    · rw [GlobalTheory.RingIface.sigO_coe l, ← map_pow, y1, GlobalTheory.RingBasics.σC_coe, hω']
    · exact GlobalTheory.AdicMaps.coeff_galois l k _ n y y3
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, map_zero, map_zero, zero_pow (pow_pos hl.out.pos s).ne']
  · obtain ⟨j, rfl⟩ := h z h0
    rw [map_pow, map_pow, h2, ← pow_mul, ← pow_mul, mul_comm]

theorem galA_wA {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s) (w : Wq l a) :
    Per.σA k (wA l a w) = wA l a ((sigma l a ^ s) w) := by
  refine WittVector.ext fun n => ?_
  refine (GlobalTheory.RingIface.sigA_coeff l k _ n).trans ?_
  change Per.σF k (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ s) w).coeff n)
  rw [coeff_sigma_pow, map_pow, galF_val hk]

variable {e : ℕ} [NeZero e]

theorem isTiltOf_kummer (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) : IsTiltOf ζ e (ϖ.kummer k) := by
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  intro n
  refine ⟨ϖ.ratio k n, ?_, ?_, ϖ.coeff_kummer k n⟩
  · rw [PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, ϖ.seq_pow, hζ,
      mul_div_cancel_right₀ _ (ϖ.seq_ne_zero 0)]
    rfl
  · refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow,
      hfix _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩), div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)),
      map_one]
    rfl

theorem emb_sigma_pow {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O) (n : ℕ)
    (τ : ZMod a) (w : Wq l a) : emb t τ ((sigma l a ^ n) w) = emb t (τ - n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ih, emb_sigma]
    congr 1
    push_cast
    ring

theorem kummer_mem_resSub (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) {ζ : Om l}
    (hζ : k (ϖ.seq 0) = ζ * ϖ.seq 0) (he : e + 1 = l ^ a) : ϖ.kummer k ∈ resSub l a := by
  rw [mem_resSub, ← he, pow_succ, GlobalTheory.MemLoc.IsTiltOf.pow_eq_one (isTiltOf_kummer ϖ hk hζ), one_mul]

theorem galA_ev (ϖ : PiSys l e) {k : GQ l} {s : ℕ} (hk : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ s)
    (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (x : (Wq l a)⟦X⟧) :
    Per.σA k (ϖ.ev a x) = ϖ.ev a (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) x)) := by
  refine RingHom.congr_fun (ringHom_ext_of_sep ((Per.σA k).comp (ϖ.ev a))
    ((ϖ.ev a).comp ((rescale (WittVector.teichmuller l z)).comp
      (PowerSeries.map ((sigma l a ^ s : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a)))) (fun w => ?_) ?_
    fun y hy => ϖ.sep_teich y fun n => ?_) x
  · simp only [RingHom.comp_apply, PiSys.ev_C, galA_wA hk, map_C]
    have : rescale (WittVector.teichmuller l z) (C ((sigma l a ^ s) w)) = C ((sigma l a ^ s) w) := by
      refine PowerSeries.ext fun m => ?_
      rw [coeff_rescale, coeff_C]
      split_ifs with h
      · rw [h, pow_zero, one_mul]
      · rw [mul_zero]
    rw [RingHom.coe_coe, this, PiSys.ev_C]
  · simp only [RingHom.comp_apply, PiSys.ev_X, map_X, rescale_X, map_mul, PiSys.ev_C, PiSys.gal_teich,
      PiSys.mu, wA_teich, hz, add_sub_cancel]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, PiSys.ev_X, PiSys.gal_teich, mul_pow]
    exact dvd_mul_left _ _

theorem thetaW_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    {ζ : ↥LL.1} (hζ : k (ϖ.seq 0) = (ζ : Om l) * ϖ.seq 0) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) :
    ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) = ζ := by
  refine Subtype.ext ((algebraMap (Om l) ℂ_[l]).injective ?_)
  have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
  simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller, hz] at h1
  exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq (isTiltOf_kummer ϖ hk hζ))

theorem toAc_rescale {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (γ : TameGal K l e a) (c : Wq l a)
    (hc : ∀ τ, algebraMap O K (emb t τ c) = γ.root τ) (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    (toAc t K (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x)) τ : K⟦X⟧) = ringAct γ (fun σ => (toAc t K x σ : K⟦X⟧)) τ := by
  refine PowerSeries.ext fun n => ?_
  rw [ringAct_apply, coeff_rescale, coeff_toAc, coeff_toAc, coeff_rescale, coeff_map, map_mul, map_pow,
    map_mul, map_pow, hc]
  congr 2
  rw [RingHom.coe_coe, emb_sigma_pow, ZMod.natCast_zmod_val]

theorem algebraMap_emb_teich (ϖ : PiSys l e) {k : GQ l} (hk : k ∈ ϖ.GKinf) (LL : FinExt l) [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a)
    (hζ : k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0) (z : Fq l a)
    (hz : Fq.val l a z = ϖ.kummer k) (τ : ZMod a) :
    algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ (WittVector.teichmuller l z)) = γ.root τ := by
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) : ↥(OL LL)) : ↥LL.1) = _
  rw [sigma_pow_teich, map_pow, SubmonoidClass.coe_pow, thetaW_teich ϖ hk LL hζ z hz, TameGal.root, powL_apply]
  simp

theorem covers_of_root {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (γ : TameGal K l e a) {k : GQ l}
    (hunr : ∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k)
    (hroot : ∀ τ, algebraMap O K (emb t τ (WittVector.teichmuller l z)) = γ.root τ) : Covers K t ϖ k γ := by
  intro f f' hf'
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) f
  set o := Module.Free.chooseBasis ℤ_[l] O
  have hf : f' = ∑ j, o j • toAc t K (rescale (WittVector.teichmuller l z)
      (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) : Wq l a →+* Wq l a) (x j))) := by
    funext τ
    refine Subtype.ext ?_
    rw [hf' τ]
    have h1 : (fun σ => (((∑ j, o j • toAc t K (x j)) σ : A O K) : K⟦X⟧)) =
        ∑ j, algebraMap O K (o j) • (fun σ => (toAc t K (x j) σ : K⟦X⟧)) := by
      funext σ
      simp [Finset.sum_apply, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
    simp [algebraMap_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toAc_rescale t γ _ hroot]
  subst hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, PiSys.iTot_toAc, galOA_tmul, galA_ev ϖ hunr z hz]

end GlobalTheory.BKGal.CoverBridge


open GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_of_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf,
    (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) →
    k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  intro l _ a e _ _ ϖ LL _ _ γ k hk hunr hζ
  have hmem := kummer_mem_resSub ϖ hk hζ (TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a))
  exact covers_of_root (thetaW a LL) ϖ γ hunr ⟨ϖ.kummer k, hmem⟩ rfl
    (algebraMap_emb_teich ϖ hk LL γ hζ ⟨ϖ.kummer k, hmem⟩ rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysFrobCoord

theorem span_range_eq_top {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  set S := Submodule.span B (Set.range u)
  obtain ⟨w, -, hu⟩ := h (N ⧸ S) 0
  have h1 := hu S.mkQ (fun x => by
    simpa using (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, rfl⟩))
  have h2 := hu 0 (fun x => by simp)
  rw [eq_top_iff]
  intro y _
  have : S.mkQ y = 0 := by rw [h1, ← h2]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem frac_indep {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    {z : LocalizedModule (Submonoid.powers d) M} {n n' : M} {k k' : ℕ} (h : IsFrac d z n k)
    (h' : IsFrac d z n' k') {b : B} (hb : lam n' = J d ^ k' * b) : lam n = J d ^ k * b := by
  unfold IsFrac at h h'
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := LocalizedModule.mk_eq.1 (h.symm.trans h')
  have h2 := congrArg lam hs
  simp only [Submonoid.smul_def, hlam, map_pow, hb] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero s hd) h2
  refine mul_left_cancel₀ (pow_ne_zero k' hd) ?_
  rw [h3]; ring

theorem frac_formula {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (φ : A →+* A)
    (Φ : M →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) M)
    (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    (F : M →+ B) (hF : ∀ r y, F (r • y) = J (φ r) * F y) (S : Set M) (hS : Submodule.span A S = ⊤)
    (h0 : ∀ y ∈ S, ∀ n k, IsFrac d (Φ y) n k → lam n = J d ^ k * F y) (y n : M) (k : ℕ)
    (h : IsFrac d (Φ y) n k) : lam n = J d ^ k * F y := by
  have key : ∀ y ∈ Submodule.span A S, ∃ n k, IsFrac d (Φ y) n k ∧ lam n = J d ^ k * F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, hn⟩ := exists_isFrac d (Φ y)
      exact ⟨n, k, hn, h0 y hy n k hn⟩
    | zero => exact ⟨0, 0, by simp [IsFrac], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, k, hn, en⟩ := hx
      obtain ⟨m, j, hm, em⟩ := hy
      refine ⟨d ^ j • n + d ^ k • m, k + j, ?_, ?_⟩
      · unfold IsFrac at hn hm ⊢
        rw [map_add (f := _), hn, hm, LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add d k j).symm
      · rw [map_add (f := _), hlam, hlam, en, em, map_add (f := _), map_pow, map_pow]; ring
    | smul r x _ hx =>
      obtain ⟨n, k, hn, en⟩ := hx
      refine ⟨φ r • n, k, ?_, ?_⟩
      · unfold IsFrac at hn ⊢
        rw [map_smulₛₗ, hn, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]
      · rw [hlam, hF, en]; ring
  obtain ⟨n', k', h', e'⟩ := key y (hS ▸ Submodule.mem_top)
  exact frac_indep d J hd lam hlam h h' e'

section Maps

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem coe_toAc_eis (τ : ZMod a) : (toAc t K (eis l a e) τ : K⟦X⟧) = E K l e := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  rw [eis, map_add (f := _), map_pow, hX, map_natCast]
  simp [E]

end Maps

theorem frob_in_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c _ hc PP hl p J g φ₂ hJp hJφ hφg hg lam hlam hlamtr y n k h τ i
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg constantCoeff h)
  have hJE : J τ (p.f (eis l a e)) = g (frob K l (E K l e)) := by
    rw [hJp, ← frob_toAc, coe_toAc_eis]
  have hJE0 : g (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hg, map_ne_zero_iff _ (frob_injective l)]; exact hE
  let lam' : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => lam y τ i, map_zero' := by simp, map_add' := by simp }
  let F : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i
      map_zero' := by simp [Matrix.mulVec, dotProduct]
      map_add' := by simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  have hJl : J τ (l : PP.A) = l := map_natCast _ _
  have := frac_formula (l : PP.A) PP.D.φ (EE.Φ PP ⟨l, hl⟩) (J τ) (hJl ▸ hl2) lam'
    (fun r y => hlam r y τ i) F ?_ _ (span_range_eq_top (EE.tr_bc p)) ?_ y n k h
  · rw [hJl] at this; exact this
  · intro r y
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlam, map_mul, hJφ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro _ ⟨x, rfl⟩ n k h
    obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x)
    obtain ⟨r, hr⟩ := EE.Φ_nat p ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ x m' k' n k hm' h
    have h1 := congrArg (fun y => lam y τ i) hr
    simp only [hlam, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hJE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hJE0 hl2)))
    rw [hlamtr, hc x m' k' hm'] at h2
    rw [hJl]
    refine mul_left_cancel₀ (pow_ne_zero k' hJE0) ?_
    change _ * lam n τ i = _
    rw [← h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlamtr, hφg,
      PhiMod.phi_apply, frobV_apply, map_mul, map_pow, map_sum, Matrix.map_apply]
    ring

end GlobalTheory.CrysFrobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodsExtensionSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.Per.DcrisSpan

open GlobalTheory.Per.TiedRestrict

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
variable {K K' LL : FinExt l} (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem le_span_restrict (T : LocTied l P AI) (hc : IsCrys (P.PD K) ρ) :
    DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ≤
      Submodule.span ↥(K0 K') (↑(DcrisK₀ (P.PD K) ρ) : Set (P.R.B ⊗[ℚ_[l]] V)) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  have hc' := isCrys_restrict h ρ T hc
  obtain ⟨h1, -⟩ := finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ
  obtain ⟨h2, -⟩ := finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))
  rw [isCrys_iff_finrank] at hc hc'
  let e : Module.Basis (Fin (Module.finrank ℚ_[l] V)) ↥(K0 K) (DcrisK₀ (P.PD K) ρ) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.finBasisOfFinrankEq ↥(K0 K) _ hc
  have hB := indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent
  let d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
    fun i => ⟨e i, dcris_le h ρ (e i).2⟩
  have hd : LinearIndependent ↥(K0 K') d :=
    LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype
      (hB.restrict_scalars' ↥(K0 K'))
  have htop : Submodule.span ↥(K0 K') (Set.range d) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hd]; simpa using hc'.symm)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))) ∈
      Submodule.span ↥(K0 K') (Set.range d) := by
    rw [htop]; trivial
  have hm := Submodule.apply_mem_span_image_of_mem_span
    (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype hx'
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact (e i).2

theorem dcris_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
    ∀ (LL : FinExt l) (T : QLat LL) (K K'' : FinExt l), K.1 ≤ K''.1 → IsCrys (P.PD K) (T.ρ.comp (inclG K)) →
      DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')) ≤
        Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) := by
  intro l _ P AI hS LL T K K'' h hc
  have eρ : T.ρ.comp (inclG K'') = (T.ρ.comp (inclG K)).comp (Subgroup.inclusion (GK_le h)) :=
    MonoidHom.ext fun _ => rfl
  rw [eρ]
  exact le_span_restrict h _ hS.some hc

end GlobalTheory.Per.DcrisSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupCoboundary
section
namespace GlobalTheory.BKCup

section Bridge

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.BKDimNoInv
open ReciprocityTheory.Gal (cycZ)

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycLL_eq (g : ↥(GK Bw.Kw)) :
    ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 g : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (Bw.e.symm g : ↥Gw) : ℤ_[l]ˣ) : ℤ_[l])) := by
  change algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
  rw [P.PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi Bw P g]
  exact (congrArg Subtype.val (Bw.eO_alg _)).symm

theorem dot_dual {O L : Type} [CommRing O] [CommRing L] (φ : O →+* L) {m : ℕ} (A : GL (Fin m) O) (ε : O)
    (x y : Fin m → L) :
    ((A : Matrix (Fin m) (Fin m) O).map φ).mulVec x ⬝ᵥ
      ((ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ).mulVec y = φ ε * (x ⬝ᵥ y) := by
  have h1 : (ε • (A : Matrix (Fin m) (Fin m) O)⁻¹.transpose).map φ =
      φ ε • (((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ).transpose := by
    ext a b
    simp
  have h2 : ((A : Matrix (Fin m) (Fin m) O)⁻¹).map φ * (A : Matrix (Fin m) (Fin m) O).map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.coe_units_inv, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [h1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem cup_cob {m : ℕ} (r r' : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hr' : Continuous fun g => ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hd : ∀ g, ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O) =
      algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]) •
        ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)⁻¹.transpose)
    (hBK : bkACore (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (c c' : ↥(GK Bw.Kw) → Fin m → ↥Bw.LL.1) (y y' : ↥Gw → Fin m → O)
    (hc : c ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r)) (hc' : c' ∈ finiteCocycles (P.PD Bw.Kw) (Bw.rep r'))
    (hy : ∀ g a, c (Bw.e g) a = Bw.toLL (y g a)) (hy' : ∀ g a, c' (Bw.e g) a = Bw.toLL (y' g a)) :
    ∃ f : ↥Gw → ↥Bw.LL.1, Continuous f ∧ ∀ g h : ↥Gw,
      Bw.toLL (y g ⬝ᵥ ((r' g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).mulVec (y' h)) =
        Bw.toLL (algebraMap ℤ_[l] O ((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  have rep_apply {s : ↥Gw →* GL (Fin m) O} (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
      Bw.rep s g x = (((s (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x := rfl
  let mkRep (s : ↥Gw →* GL (Fin m) O)
      (hs : Continuous fun g => ((s g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
      GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) := by
    haveI : IsTopologicalRing ↥Bw.LL.1 := hG.2.2.2.1
    exact { V := Fin m → ↥Bw.LL.1
            acg := inferInstance
            modLL := inferInstance
            modQp := inferInstance
            towQp := inferInstance
            modO := inferInstance
            towO := inferInstance
            fd := inferInstance
            top := inferInstance
            mtop := inferInstance
            cadd := inferInstance
            csmul := inferInstance
            ρ := Bw.rep s
            cont := by
              intro x
              simp only [rep_apply]
              exact ((hs.comp Bw.e_symm_cont).matrix_map
                (continuous_subtype_val.comp Bw.eO_cont)).matrix_mulVec continuous_const }
  let A := mkRep r hr
  let A' := mkRep r' hr'
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  let Q : (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] (Fin m → ↥Bw.LL.1) →ₗ[↥Bw.LL.1] ↥Bw.LL.1 :=
    dotProductBilin ↥Bw.LL.1 ↥Bw.LL.1
  have hD : IsDual1 (P.PD Bw.Kw) (Bw.rep r) (Bw.rep r') Q := by
    refine ⟨fun g x z => ?_, fun x hx => ?_, fun z hz => ?_, rfl⟩
    · change Bw.rep r g x ⬝ᵥ Bw.rep r' g z = _ * (x ⬝ᵥ z)
      rw [rep_apply, rep_apply, hd, dot_dual, cycLL_eq]
    · exact dotProduct_eq_zero x hx
    · exact dotProduct_eq_zero z fun x => (dotProduct_comm _ _).trans (hz x)
  obtain ⟨f, hf, hf'⟩ := (((hBK _ _ hG A A' Q hA hD).1 c hc.1).1 hc) c' hc'
  refine ⟨f ∘ Bw.e, hf.comp Bw.e_cont, fun g h => ?_⟩
  have h1 : ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) * f (Bw.e h) - f (Bw.e g * Bw.e h) +
      f (Bw.e g) = c (Bw.e g) ⬝ᵥ Bw.rep r' (Bw.e g) (c' (Bw.e h)) := congrFun hf' (Bw.e g, Bw.e h)
  rw [cycLL_eq, rep_apply, MulEquiv.symm_apply_apply, ← map_mul] at h1
  refine Eq.trans ?_ h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, hy, hy']

end Bridge

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem cup_coboundary : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (c c' : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1) (y y' : ↥(DecV N v) → Fin D.R.r → X.O0 i), c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) → c' ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ) → (∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a)) → (∀ g a, c' ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y' g a)) → ∃ f : ↥(DecV N v) → ↥(bkP.br i v hv).LL.1, Continuous f ∧ ∀ g h : ↥(DecV N v), (bkP.br i v hv).toLL (y g ⬝ᵥ ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).mulVec (y' h)) = (bkP.br i v hv).toLL (algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])) * f h - f (g * h) + f g := by
  intro D N X bkP i s h ρ hρ v hv c c' y y' hc hc' hy hy'
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  refine cup_cob (bkP.br i v hv) (D.loc (X.l i)) ((Tgl i s).comp (DecV N v).subtype) (ρ.comp (DecV N v).subtype)
    ?_ ?_ (fun g => ?_) (h.2.2.2.2.2.1 _ _).1 (h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1 c c' y y' hc hc' hy hy'
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tmat i s).comp continuous_subtype_val).congr fun g => (Tgl_coe i s g).symm
  · exact ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp continuous_subtype_val).congr fun g => (hρ g).symm
  · refine (hρ g).trans ?_
    rw [Tdual, ← Tgl_coe]
    rfl

end GlobalTheory.BKCup
end

