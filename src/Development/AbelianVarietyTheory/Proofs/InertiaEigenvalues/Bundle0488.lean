module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace BridgeWittDvd

section Witt
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem dvd_iff (x : WittVector p k) : (p : WittVector p k) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton]
  exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

theorem exists_limit (w : ℕ → WittVector p k) (h : ∀ n, (p : WittVector p k) ^ n ∣ w (n + 1) - w n) :
    ∃ z : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ z - w n := by
  have hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance
  have key : ∀ (n : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        (p : WittVector p k) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih
  obtain ⟨z, hz⟩ := hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, ← dvd_neg, neg_sub]
    exact step m d)
  refine ⟨z, fun n => ?_⟩
  rw [← dvd_neg, neg_sub]
  exact (key n _ _).1 (hz n)

theorem series_dvd (s : (WittVector p k)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := p) (R := k)) s = 0) :
    (p : (WittVector p k)⟦X⟧) ∣ s := by
  have hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c := by
    intro n
    apply (dvd_iff _).2
    have := congrArg (PowerSeries.coeff n) h
    simpa using this
  choose c hc using hd
  refine ⟨PowerSeries.mk c, ?_⟩
  ext1 n
  rw [← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem decomp (w : WittVector p k) (h0 : w ≠ 0) :
    ∃ (n : ℕ) (v : WittVector p k), IsUnit v ∧ w = (p : WittVector p k) ^ n * v := by
  obtain ⟨n, v, e⟩ := WittVector.exists_eq_pow_p_mul' w h0
  exact ⟨n, v, v.isUnit, e⟩
end Witt

theorem perfect_frac (p : ℕ) [Fact p.Prime] (R F : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CharP R p] [CharP F p] [PerfectRing R p] : PerfectRing F p := by
  refine PerfectRing.ofSurjective F p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨a', rfl⟩ := (bijective_frobenius R p).2 a
  obtain ⟨b', rfl⟩ := (bijective_frobenius R p).2 b
  exact ⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩

end BridgeWittDvd

theorem Bridge.kisin_reduction_unit_at_uniformizer : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (K : Formalism.BasicNotions.Loc.FinExt l) (bk : GlobalTheory.BSP.BK K), (∀ w ∈ bk.OE, l.cast ∣ w → ∃ v ∈ bk.OE, w = l.cast * v) ∧ (∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW PowerSeries.X : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ (s : bk.S), ¬l.cast ∣ s → ∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW s : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ w ∈ bk.OE, w ≠ OfNat.ofNat 0 → ∃ (k : ℕ) (v : Formalism.BasicNotions.Loc.WCb l) (v' : Formalism.BasicNotions.Loc.WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = OfNat.ofNat 1 ∧ w = HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast k * v) ∧ (∀ (w : ℕ → Formalism.BasicNotions.Loc.WCb l), (∀ (n : ℕ), w n ∈ bk.OE) → (∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ w (n + OfNat.ofNat 1) - w n) → ∃ z ∈ bk.OE, ∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ z - w n) ∧ (∀ (g : ↥(Formalism.BasicNotions.Loc.GK K)), bk.FixFlat g → ∀ w ∈ bk.OE, DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (F := Formalism.BasicNotions.Loc.GQ l →* Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (GlobalTheory.Prism.galW l) (g.val (p := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ x ∈ Formalism.BasicNotions.Loc.GK K)) : Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) w = w) ∧ ∀ w ∈ bk.OE, Membership.mem (α := Formalism.BasicNotions.Loc.WCb l) bk.OE (DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l →ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (Formalism.BasicNotions.Loc.frobW l) w : Formalism.BasicNotions.Loc.WCb l) := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)
  obtain ⟨ek, -, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨-, hS, hX, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨hsat, hcl, hφ, hgal, hunit⟩ := _root_.GlobalTheory.OEStable.main l K bk
  have hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_assoc] at hv
      exact hsat v (ih _ hv)
  refine ⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩
  · rintro w hw ⟨v, rfl⟩
    exact ⟨v, hsat v hw, rfl⟩
  · intro s hs
    refine hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)
    apply BridgeWittDvd.series_dvd
    apply hinj
    rw [hek, map_zero]
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := rfl
    rw [e] at h0
    exact (FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)
  · intro w hw h0
    obtain ⟨n, v, hv, e⟩ := BridgeWittDvd.decomp (p := l) (k := Cb l) w h0
    have hvO : v ∈ bk.OE := hsatn n v (e ▸ hw)
    obtain ⟨v', hv', e'⟩ := hunit v hvO hv
    exact ⟨n, v, v', hvO, hv', e', e⟩
  · intro w hw h
    obtain ⟨z, hz⟩ := BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h
    exact ⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩

namespace GlobalTheory.OEDvr

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

variable {K : FinExt l} (bk : BK K)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) :=
  Bridge.kisin_reduction_unit_at_uniformizer

end GlobalTheory.OEDvr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantLatticeFiltrationZero
section
section
open scoped Formalism.Per

namespace Bridge.FilZeroMul

theorem mul_mem_div_self {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (N : Submodule R A) {x y : A} (hx : x ∈ N / N) (hy : y ∈ N / N) : x * y ∈ N / N := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx hy ⊢
  intro z hz
  rw [mul_assoc]
  exact hx _ (hy z hz)

theorem mul_mem_filD_zero (l : ℕ) [Fact l.Prime] {x y : Formalism.Per.BdR l}
    (hx : x ∈ Formalism.Per.FilD l 0) (hy : y ∈ Formalism.Per.FilD l 0) : x * y ∈ Formalism.Per.FilD l 0 :=
  mul_mem_div_self (Reformulated.AutPerF.BdR.filNat l (Formalism.Per.OC l) 0) hx hy

end Bridge.FilZeroMul

theorem Bridge.mul_mem_filtration_zero : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O : Type} [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) {x y : GlobalTheory.BKReal.OB l O}, x ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → x * y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 := by
  intro l _ O _ _ C x y hx hy
  unfold GlobalTheory.BKGal.XiFil.filO at hx hy ⊢
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨a * b, ?_, ?_⟩
  · rw [map_mul]
    exact Bridge.FilZeroMul.mul_mem_filD_zero l ha hb
  · simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil.ImageFil

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem mul_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x y : OB l O} (hx : x ∈ filO O C 0)
    (hy : y ∈ filO O C 0) : x * y ∈ filO O C 0 := by
  exact Bridge.mul_mem_filtration_zero C hx hy

theorem toOB_mem_filO (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul o w =>
    have h : toOB l O (o ⊗ₜ w) = o • ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [h]
    refine Submodule.smul_mem _ o (Submodule.subset_span ⟨acrisToBcris l w, ?_, rfl⟩)
    rw [mem_FilD_zero_iff]
    exact ⟨C.j w, C.ι_j w⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem pow_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x : OB l O} (hx : x ∈ filO O C 0) (n : ℕ) :
    x ^ n ∈ filO O C 0 := by
  induction n with
  | zero =>
    rw [pow_zero, ← map_one (toOB l O)]
    exact toOB_mem_filO C 1
  | succ n ih => rw [pow_succ]; exact mul_mem_filO_zero C ih hx

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  simpa using (GlobalTheory.RingBasics.isUnit_l (l := l)).map (algebraMap (Per.AinfP l) (Per.BdRp l))

theorem exists_inv_l_mem (C : GlobalTheory.MemLoc.Core l) : ∃ r ∈ filO O C 0, r * (l : OB l O) = 1 := by
  obtain ⟨β, hβ⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_left_inv
  obtain ⟨z, hz⟩ := (isUnit_l_BdRp (l := l)).exists_left_inv
  refine ⟨(1 : O) ⊗ₜ β, Submodule.subset_span ⟨β, ?_, rfl⟩, ?_⟩
  · rw [mem_FilD_zero_iff]
    refine ⟨z, ?_⟩
    have h1 : C.ι β * ((l : ℕ) : Per.BdR l) = 1 := by rw [← map_natCast C.ι, ← map_mul, hβ, map_one]
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) z * ((l : ℕ) : Per.BdR l) = 1 := by
      rw [← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_mul, hz, map_one]
    calc C.ι β = C.ι β * (((l : ℕ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) z) := by
          rw [mul_comm ((l : ℕ) : Per.BdR l), h2, mul_one]
      _ = algebraMap (Per.BdRp l) (Per.BdR l) z := by rw [← mul_assoc, h1, one_mul]
  · rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : Per.Bcris l) from
      (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hβ]
    rfl

variable {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem iSl_mem_filO (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (p : invL l (S O K e)) :
    ϖ.iSl O K p ∈ filO O C 0 := by
  obtain ⟨f, n, hf⟩ := p
  have h1 : (l : invL l (S O K e)) ^ n * ⟨f, n, hf⟩ = ⟨_, le_away _ _ hf⟩ := Subtype.ext (by simp)
  have h2 := congrArg (ϖ.iSl O K) h1
  rw [map_mul, map_pow, map_natCast, ϖ.iSl_of_mem O K hf] at h2
  obtain ⟨r, hr, hrl⟩ := exists_inv_l_mem (O := O) C
  have h3 : ϖ.iSl O K ⟨f, n, hf⟩ = r ^ n * toOB l O (ϖ.iS O K ⟨_, hf⟩) := by
    rw [← h2, ← mul_assoc, ← mul_pow, hrl, one_pow, one_mul]
  rw [h3]
  exact mul_mem_filO_zero C (pow_mem_filO_zero C hr n) (toOB_mem_filO C _)

end GlobalTheory.BKGal.XiFil.ImageFil

namespace GlobalTheory.BKGal.XiFil


open GlobalTheory.BKGal.XiFil.ImageFil in
theorem iB_mem_filO_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)), ϖ.iB t K f ∈ filO O C 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ C f
  rw [PiSys.iB, glue_apply]
  refine Submodule.sum_mem _ fun τ _ => mul_mem_filO_zero C ?_ (iSl_mem_filO K ϖ C (f τ))
  rw [idem, constB, AlgHom.comp_apply]
  exact toOB_mem_filO C _

end GlobalTheory.BKGal.XiFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummand

open Module TensorProduct
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

theorem exists_isCompl_of_saturated {O M : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (h : ∀ (a : O) (x : M), a ≠ 0 → a • x ∈ N → x ∈ N) : ∃ C : Submodule O M, IsCompl N C := by
  first
  | exact @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated
  | (apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedComplement.exists_isCompl_of_saturated ..)

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL]

section Rep

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {ρ : Representation LL G V}


variable [Module O V] [IsScalarTower O LL V] [IsDomain O] [IsFractionRing O LL]


omit [TopologicalSpace G] in
theorem invariants_stableLattice_mod_irreducible_eq_bot [IsDiscreteValuationRing O] (L : Lattice (O := O) ρ) {lam : O} (hlam : Irreducible lam)
    (h : (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants = ⊥) : H0V ρ = ⊥ := by
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hsm : ∀ (a : O) (x : V), a ≠ 0 → a • x = 0 → x = 0 := fun a x ha hx => by
    rw [← algebraMap_smul LL] at hx
    exact (smul_eq_zero.1 hx).resolve_left (by simpa using ha)
  have hM : (latRep L).invariants = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) _ (IsNoetherian.noetherian _) ?_ ?_
    · intro x hx
      have h1 : x ⊗ₜ[O] (1 : O ⧸ Ideal.span {lam}) ∈
          (coefRep (latRep L) (O ⧸ Ideal.span {lam})).invariants := fun g => by
        rw [coefRep_tmul, hx g]
      rw [h, Submodule.mem_bot] at h1
      have h2 := congrArg (TensorProduct.tensorQuotEquivQuotSMul ↥L.T (Ideal.span {lam})) h1
      rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul] at h2
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x lam ⊤).1 h2
      refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) fun g => Subtype.ext ?_
      have h3 := congrArg Subtype.val (hx g)
      rw [map_smul] at h3
      refine sub_eq_zero.1 (hsm lam _ hlam.ne_zero ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h3
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hlam.maximalIdeal_eq]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha, hax⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
  have h1 : (⟨a • x, hax⟩ : ↥L.T) ∈ (latRep L).invariants := fun g => Subtype.ext (by
    have := (Submodule.mem_iInf _).1 hx g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    change ρ g (a • x) = a • x
    rw [← algebraMap_smul LL, map_smul, this])
  rw [hM, Submodule.mem_bot] at h1
  exact hsm a x ha (congrArg Subtype.val h1)

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem h1fT_saturated (L : Lattice (O := O) ρ) (a : O) (x : LatticeCohomology L) (ha : a ≠ 0) (hx : a • x ∈ latticeFiniteCohomology PD L) :
    x ∈ latticeFiniteCohomology PD L := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c', hc', h⟩ := hx
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨b, -, hb⟩ := h
  have h1 : ((c' - a • c : ↥(latticeCocycles L)) : G → V) ∈ finiteCocycles PD ρ := by
    refine ⟨(c' - a • c).2.1, b ⊗ₜ 1, fun g => ?_⟩
    have : ρ g b - b = ((c' - a • c : ↥(latticeCocycles L)) : G → V) g := congrFun hb g
    rw [← this]
    simp [actVB, sub_tmul]
  have h2 : algebraMap O LL a • (c : G → V) ∈ finiteCocycles PD ρ := by
    have := (finiteCocycles PD ρ).sub_mem hc'.2 h1
    rw [algebraMap_smul]
    simpa using this
  have ha' : algebraMap O LL a ≠ 0 := by simpa using ha
  have h3 : (c : G → V) ∈ finiteCocycles PD ρ := (Submodule.smul_mem_iff (finiteCocycles PD ρ) ha').1 h2
  exact ⟨c, ⟨c.2, h3⟩, rfl⟩

theorem finrank_h1fT [CompactSpace G] (L : Lattice (O := O) ρ) (hT : IsOpen (L.T : Set V)) :
    finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD ρ) := by
  refine congrArg Cardinal.toNat (GlobalTheory.BlochKatoRank.rank_subquotient_eq (K := LL) LinearMap.id (latticeCocycles L) (latticeCoboundaries L)
    (latticeFiniteCocycles PD L) (finiteCocycles PD ρ) (B1 ρ) (fun a ha => ha.2) ?_ ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, hx⟩
    obtain ⟨m, hm, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L x
    refine ⟨m, hm, m • x, h, ?_⟩
    rw [map_smul]
    exact congrArg (m • ·) hx
  · intro c hc
    obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1.1
    have h1 : a • c ∈ (finiteCocycles PD ρ).restrictScalars O :=
      Submodule.smul_mem ((finiteCocycles PD ρ).restrictScalars O) a hc
    exact ⟨a, ha, a • c, ⟨h1.1, fun g _ => h g⟩, ⟨⟨h1.1, fun g _ => h g⟩, h1⟩, rfl⟩

end Rep

end General


end GlobalTheory.TopSteps.FinSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleMapUnramifiedWittToFractionFieldOfEis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.TameFrob

open Polynomial

attribute [local instance] algK isFractionRing

theorem irreducible_map_iota_of_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := by
  intro l _ a _ E hmon hdeg hdiv ⟨w, hw⟩
  have hP : (Ideal.span {(l : Wq l a)}).IsPrime := by
    rw [← WittVector.ker_constantCoeff]; exact RingHom.ker_isPrime _
  have hl0 : (l : Wq l a) ≠ 0 := fun h => by
    have := congrArg (iotaO l a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hW : Irreducible E := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive hdeg
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (hdiv n hn)
    · rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : (l : Wq l a) * ((w : Wq l a) - l * c) = 0 := by linear_combination hc
      have h2 : (w : Wq l a) = l * c := by
        have := (mul_eq_zero.1 h1).resolve_left hl0
        linear_combination this
      have h3 := congrArg WittVector.constantCoeff h2
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at h3
      exact (w.isUnit.map WittVector.constantCoeff).ne_zero h3
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 hW
  exact h

end GlobalTheory.TameFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f : Hom bk.prism B),
    IsFrame bk B (BK.hf (bk := bk) f bk.E) (BK.hf (bk := bk) f X) := by
  intro l _ K bk B f
  have hI : bk.prism.I.map f.f = B.I :=
    GlobalTheory.T.prism_hom_map_ideal_eq l _ bk.prism B f
  refine ⟨hI.symm.trans ?_, ?_⟩
  · change (Ideal.span {bk.E}).map (BK.hf (bk := bk) f) = _
    rw [Ideal.map_span, Set.image_singleton]
  · apply f.f_str
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str.toRingHom (bk.str.symm _)
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBoundsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layer_DdR_bounds_alt : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ) (N : ℕ), (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → (∀ τ, ∀ n ∈ J τ, |n| ≤ N) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) := by
  first | exact @GlobalTheory.LayerJumps.layer_DdR_bounds | exact GlobalTheory.LayerJumps.layer_DdR_bounds | (intros; apply GlobalTheory.LayerJumps.layer_DdR_bounds <;> assumption)
end

