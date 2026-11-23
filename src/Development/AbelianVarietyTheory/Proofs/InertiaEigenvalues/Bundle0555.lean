module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiscBasisCrystallineLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem height_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_radius_pos_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SatInvUnit

theorem perfectRing_tilt_fraction_field (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ l fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
    simp [frobenius_def, div_pow, map_pow]⟩

theorem constantCoeff_frobW (l : ℕ) [Fact l.Prime] (x : WCb l) :
    WittVector.constantCoeff (frobW l x) = frobenius (Cb l) l (WittVector.constantCoeff x) :=
  WittVector.map_coeff (frobenius (Cb l) l) x 0

theorem constantCoeff_galW (l : ℕ) [Fact l.Prime] (g : GQ l) (x : WCb l) :
    WittVector.constantCoeff (galW l g x) = autCb l (galTilt l g) (WittVector.constantCoeff x) :=
  WittVector.map_coeff (autCb l (galTilt l g)).toRingHom x 0

end GlobalTheory.SatInvUnit

namespace GlobalTheory.SatInvUnit

theorem isUnit_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A →
    (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) →
    (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) →
    IsUnit Y := by
  intro l _ K bk d Y A hY hA hφ hg hsat
  haveI : PerfectRing (Cb l) l := perfectRing_tilt_fraction_field l
  set c : WCb l →+* Cb l := WittVector.constantCoeff (p := l) (R := Cb l) with hc

  have hdetA : IsUnit A.det := by
    obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y.det hY
    have h1 : frobW l Y.det = Y.det * A.det := by
      rw [← Matrix.det_mul, ← hφ]
      simpa using RingHom.map_det (frobW l).toRingHom Y
    have hlm : ((l : WCb l)) ^ m ≠ 0 := left_ne_zero_of_mul (hu ▸ hY)
    rw [hu, map_mul, map_pow, map_natCast, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hlm h1
    have hfu : IsUnit (frobW l (u : WCb l)) := u.isUnit.map (frobW l)
    rw [h2] at hfu
    exact isUnit_of_mul_isUnit_right hfu
  have hcA : (A.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdetA.map c).ne_zero
  by_cases h0 : (Y.map c).det = 0
  · exfalso
    have hAm : ∀ i j, (A.map c) i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) :=
      fun i j => Subring.mem_map.2 ⟨A i j, hA i j, rfl⟩
    have hφ' : (Y.map c).map (frobenius (Cb l) l) = Y.map c * A.map c := by
      have : (Y.map (frobW l)).map c = (Y.map c).map (frobenius (Cb l) l) := by
        ext i j
        exact constantCoeff_frobW l (Y i j)
      rw [← this, hφ, Matrix.map_mul]
    have hg' : ∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧
        R * (Y.map c).map (autCb l (galTilt l (g : GQ l))) = Y.map c := by
      intro g hfix
      obtain ⟨R, hR, hRY⟩ := hg g hfix
      refine ⟨R.map c, hR.map c.mapMatrix, ?_⟩
      have : (Y.map (galW l (g : GQ l))).map c = (Y.map c).map (autCb l (galTilt l (g : GQ l))) := by
        ext i j
        exact constantCoeff_galW l (g : GQ l) (Y i j)
      rw [← this, ← Matrix.map_mul, hRY]
    obtain ⟨vb, hv0, hvm, hYv⟩ := GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable l K bk d (Y.map c) (A.map c) hcA hAm hφ' hg' h0
    choose v hv hvc using fun i => Subring.mem_map.1 (hvm i)
    have hdiv : ∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i := by
      intro i
      rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
      change c (Y.mulVec v i) = 0
      rw [RingHom.map_mulVec]
      have : (c ∘ v) = vb := funext fun j => hvc j
      rw [this, hYv]
      rfl
    apply hv0
    funext i
    obtain ⟨r, hr⟩ := hsat v hv hdiv i
    rw [← hvc i, hr, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    rfl
  · have hu : IsUnit Y.det := by
      apply WittVector.isUnit_of_coeff_zero_ne_zero
      intro h
      apply h0
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact h
    exact (Matrix.isUnit_iff_isUnit_det Y).2 hu

end GlobalTheory.SatInvUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModSpanSUnionLeOfDirected
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.Pass.LocDirect

theorem lenMod_span_sUnion_le_of_directed : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞),
    (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) →
    (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) →
    BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  intro O M _ _ _ S H N hdir hA
  classical
  apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset
  intro F hF
  rcases S.eq_empty_or_nonempty with hS | ⟨A0, hA0⟩
  · have hF0 : (↑F : Set M) = ∅ := by
      rw [hS, Set.sUnion_empty] at hF
      exact Set.subset_empty_iff.mp hF
    rw [hF0, Submodule.span_empty, GlobalTheory.Pass.LocDual.lenMod_eq_height_map, Submodule.map_bot,
      Order.height_bot]
    exact zero_le
  · have key : ∀ G : Finset M, (↑G : Set M) ⊆ ⋃₀ S → ∃ A ∈ S, (↑G : Set M) ⊆ A := by
      intro G
      induction G using Finset.induction_on with
      | empty => intro _; exact ⟨A0, hA0, by simp⟩
      | insert a G ha ih =>
        intro hG
        rw [Finset.coe_insert, Set.insert_subset_iff] at hG
        obtain ⟨B, hB, haB⟩ := hG.1
        obtain ⟨A, hA', hGA⟩ := ih hG.2
        obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA' B hB
        refine ⟨C, hC, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hBC haB, hGA.trans hAC⟩
    obtain ⟨A, hAS, hFA⟩ := key F hF
    refine le_trans ?_ (hA A hAS)
    rw [GlobalTheory.Pass.LocDual.lenMod_eq_height_map, GlobalTheory.Pass.LocDual.lenMod_eq_height_map]
    exact Order.height_mono (Submodule.map_mono (Submodule.span_mono hFA))

end GlobalTheory.Pass.LocDirect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftStratifiedSolutionSuccOfCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mem_span_range_of_isBaseChange {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (w : N) : w ∈ Submodule.span S (Set.range f) := by
  obtain ⟨y, rfl⟩ := hf.equiv.surjective w
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s x => rw [hf.equiv_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem le_of_span_eq_top_of_isBaseChange {R S N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (P Q : Submodule R N) (hPQ : P ≤ Q) (hQ : IsBaseChange S Q.subtype)
    (hP : Submodule.span S (P : Set N) = ⊤) : Q ≤ P := by
  let ι := Submodule.inclusion hPQ
  have hs : Function.Surjective (ι.lTensor S) := by
    intro y
    have hv : hQ.equiv y ∈ Submodule.span S (P : Set N) := hP ▸ Submodule.mem_top
    have key : ∀ v ∈ Submodule.span S (P : Set N), ∃ y' : S ⊗[R] P, hQ.equiv (ι.baseChange S y') = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact ⟨1 ⊗ₜ ⟨x, hx⟩, by simp [ι, hQ.equiv_tmul]⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by simp [ha, hb]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c • a, by simp [ha]⟩
    obtain ⟨y', hy'⟩ := key _ hv
    exact ⟨y', by rw [← LinearMap.baseChange_eq_ltensor]; exact hQ.equiv.injective hy'⟩
  have hι := (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S ι).mp hs
  intro x hx
  obtain ⟨y, hy⟩ := hι ⟨x, hx⟩
  have hx' : (y : N) = x := congrArg Subtype.val hy
  exact hx' ▸ y.2

theorem lift_solution_succ_of_descent {l : ℕ} {R : Type} [CommRing R] {d : ℕ} {B C D : Obj l R} (h : Hom B C)
    (p q : Hom C D) (hcomm : p.comp h = q.comp h) (m : ℕ) (hff : (qmap h m).FaithfullyFlat)
    (ε : Matrix (Fin d) (Fin d) D.A)
    (H : ∀ k : ℕ, letI := (qmap h k).toAlgebra
      ∃ N : Submodule (B.A ⧸ adI B ^ k) (Fin d → C.A ⧸ adI C ^ k),
        (∀ z, z ∈ N ↔ (fun i => qmap p k (z i)) =
          (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec fun i => qmap q k (z i)) ∧
        IsBaseChange (C.A ⧸ adI C ^ k) N.subtype)
    (z : Fin d → C.A) (hz : ∀ i, p.f (z i) - ε.mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧
      ∀ i, p.f (z' i) - ε.mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  have hmem : ∀ (k : ℕ) (w : Fin d → C.A),
      ((fun i => qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i))) =
        (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i)))) ↔
      ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ k := by
    intro k w
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    have e1 : qmap p k (Ideal.Quotient.mk (adI C ^ k) (w i)) = Ideal.Quotient.mk (adI D ^ k) (p.f (w i)) :=
      qmap_mk p k _
    have e2 : (ε.map (Ideal.Quotient.mk (adI D ^ k))).mulVec
        (fun i => qmap q k (Ideal.Quotient.mk (adI C ^ k) (w i))) i =
        Ideal.Quotient.mk (adI D ^ k) (ε.mulVec (fun j => q.f (w j)) i) := by
      simp only [qmap_mk]
      exact (RingHom.map_mulVec (Ideal.Quotient.mk (adI D ^ k)) ε (fun j => q.f (w j)) i).symm
    rw [e1, e2]
    exact Ideal.Quotient.eq
  letI alg0 : Algebra (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := (qmap h m).toAlgebra
  letI alg1 : Algebra (B.A ⧸ adI B ^ (m + 1)) (C.A ⧸ adI C ^ (m + 1)) := (qmap h (m + 1)).toAlgebra
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ m) (C.A ⧸ adI C ^ m) := hff
  obtain ⟨N, hN, hbN⟩ := H m
  obtain ⟨N', hN', hbN'⟩ := H (m + 1)
  have hpq : ∀ b : B.A, p.f (h.f b) = q.f (h.f b) := fun b => congrArg (fun g : Hom B D => g.f b) hcomm
  let P : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m) :=
    { carrier := {x | ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = x ∧
        ∀ i, p.f (w i) - ε.mulVec (fun j => q.f (w j)) i ∈ adI D ^ (m + 1)}
      zero_mem' := ⟨0, by funext i; simp, fun i => by
        have e : (fun j => q.f ((0 : Fin d → C.A) j)) = 0 := funext fun j => by simp
        rw [e, Matrix.mulVec_zero]
        simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
        refine ⟨w₁ + w₂, by funext i; simp, fun i => ?_⟩
        have := Ideal.add_mem _ (h₁ i) (h₂ i)
        convert this using 1
        have e : (fun j => q.f ((w₁ + w₂) j)) = (fun j => q.f (w₁ j)) + (fun j => q.f (w₂ j)) := by
          funext j; simp
        rw [e, Matrix.mulVec_add]
        simp only [Pi.add_apply, map_add (f := _)]
        ring
      smul_mem' := by
        rintro c _ ⟨w, rfl, hw⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        refine ⟨fun i => h.f b * w i, ?_, fun i => ?_⟩
        · funext i
          simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, qmap_mk]
        · have := Ideal.mul_mem_left _ (q.f (h.f b)) (hw i)
          convert this using 1
          have e : (fun j => q.f (h.f b * w j)) = q.f (h.f b) • (fun j => q.f (w j)) := by
            funext j; simp
          rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, hpq, mul_sub] }
  have hPN : P ≤ N := by
    rintro _ ⟨w, rfl, hw⟩
    exact (hN _).2 ((hmem m w).2 fun i => Ideal.pow_le_pow_right (Nat.le_succ m) (hw i))
  have hspan : Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    let πC := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m) : adI C ^ (m + 1) ≤ adI C ^ m)
    let r : (Fin d → C.A ⧸ adI C ^ (m + 1)) → (Fin d → C.A ⧸ adI C ^ m) := fun y i => πC (y i)
    have hr : ∀ y ∈ Submodule.span (C.A ⧸ adI C ^ (m + 1)) (Set.range N'.subtype),
        r y ∈ Submodule.span (C.A ⧸ adI C ^ m) (P : Set (Fin d → C.A ⧸ adI C ^ m)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨x, hxN⟩, rfl⟩ := hx
        apply Submodule.subset_span
        obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk _ (w i)) = x :=
          ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
            funext fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec⟩
        exact ⟨w, by funext i; simp [r, πC], (hmem (m + 1) w).1 ((hN' _).1 hxN)⟩
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i; simp [r]
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy using 1
        funext i; simp [r]
      | smul c x _ hx =>
        convert Submodule.smul_mem _ (πC c) hx using 1
        funext i; simp [r]
    obtain ⟨w, rfl⟩ : ∃ w : Fin d → C.A, (fun i => Ideal.Quotient.mk (adI C ^ m) (w i)) = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    have := hr (fun i => Ideal.Quotient.mk _ (w i)) (mem_span_range_of_isBaseChange hbN' _)
    convert this using 1
    funext i; simp [r, πC]
  have hNP : N ≤ P := le_of_span_eq_top_of_isBaseChange P N hPN hbN hspan
  have hzN : (fun i => Ideal.Quotient.mk (adI C ^ m) (z i)) ∈ N := (hN _).2 ((hmem m z).2 hz)
  obtain ⟨w, hw, hwE⟩ := hNP hzN
  exact ⟨w, fun i => Ideal.Quotient.eq.1 (congrFun hw i), hwE⟩

theorem lift_solution_succ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ (m : ℕ) (z : Fin d → C.A), (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ m) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ m) ∧ ∀ i, p.f (z' i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) i ∈ adI D ^ (m + 1) := by
  intro l _ K bk d S B C D h f p q hcov hpo m z hz
  refine lift_solution_succ_of_descent h p q hpo.comm m (hcov.ff m) _ (fun k => ?_) z hz
  exact (GlobalTheory.T.stratifiedPhiModule_descent_finite_level l K bk d S B C D h f p q hcov hpo k).imp fun N hN => ⟨hN.1, hN.2.2.2⟩

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGamma
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CocycleInj


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  intro D HW F l _ K s LL h W E T hT M m hy hz
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius D HW F l K s LL h T hT M m hy
  exact GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma D HW F l K s LL h T hT M a m hy hz ha

end GlobalTheory.NL.CocycleInj
end

