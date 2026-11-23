module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalOneSubOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSelmerLengthsEqDeterminantValuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBRamifiedPrimesNeTypePrimes
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.TypePrimesQD

theorem not_split_of_ram_two (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2)
    (hsplit : (placesOver E l).ncard = Module.finrank ℚ E) : False := by
  classical
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (placesOver E l).Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨hdpos, hsum⟩ := GlobalTheory.Proof.LocDegPos.locDeg_pos_and_sum_le E l hl
  have hle := hsum hfin.toFinset (fun v hv => hfin.mem_toFinset.1 hv)
  have hge : ∑ v ∈ hfin.toFinset, 2 ≤ ∑ v ∈ hfin.toFinset, Formalism.MainNotions.N.locDeg E v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have h2 := hram v (hfin.mem_toFinset.1 hv)
    have hp := hdpos v
    unfold Formalism.MainNotions.N.locDeg at hp ⊢
    rw [h2] at hp ⊢
    omega
  rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hsplit] at hge
  omega

theorem qd_ne_typePrimes : ∀ (D : D7), Formalism.MainNotions.EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := by
  intro D h1 i hl
  have key : ∀ k : Fin 2, D.nd.l i ≠ D.host.g k := by
    intro k hk
    have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
      rcases hl with h | h <;> simp [h]
    have hram := (h1 _ hmem).2
    rw [hk] at hram
    exact not_split_of_ram_two D.host.E (D.host.g k) (D.host.g_prime k)
      (fun v hv => (hram v hv).1) (D.nd.g_split k)
  exact ⟨key 0, key 1⟩

end GlobalTheory.Proof.TypePrimesQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TwoCopy

variable {l : ℕ} [hl : Fact l.Prime]

theorem dvd_pow_of_ne_zero {π b : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (hb : b ≠ 0) :
    ∃ n : ℕ, b ∣ π ^ n := by
  haveI := GlobalTheory.FrobInt.valuationRing_tilt l
  by_contra h
  push_neg at h
  apply hb
  refine hπ.haus b fun n => ?_
  obtain ⟨c, hc⟩ : π ^ n ∣ b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond b (π ^ n)
    · exact absurd ⟨c, hc.symm⟩ (h n)
    · exact ⟨c, hc.symm⟩
  rw [SModEq.zero, hc, ← smul_eq_mul]
  exact Submodule.smul_mem_smul (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    Submodule.mem_top

theorem isUnit_of_ne_zero {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) (y : OCb l) (hy : y ≠ 0) : IsUnit (i y) := by
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ hy
  exact isUnit_of_mul_isUnit_left (y := i c) (by rw [← map_mul, ← hc, map_pow]; exact hu.pow n)

theorem exists_ext {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) :
    ∃ j : Cb l →+* T, ∀ y, j (algebraMap (OCb l) (Cb l) y) = i y :=
  ⟨IsLocalization.lift (M := nonZeroDivisors (OCb l)) (S := Cb l) (g := i)
      fun y => isUnit_of_ne_zero hπ i hu y (nonZeroDivisors.ne_zero y.2),
    fun y => IsLocalization.lift_eq _ y⟩

theorem exists_clear {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (x : Cb l) :
    ∃ (n : ℕ) (y : OCb l), algebraMap (OCb l) (Cb l) π ^ n * x = algebraMap (OCb l) (Cb l) y := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (OCb l)) x
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ (nonZeroDivisors.ne_zero b.2)
  refine ⟨n, c * a, ?_⟩
  simp only at h
  rw [← map_pow, hc, map_mul, map_mul, ← h]
  ring

theorem exists_clear_family {κ : Type} [Fintype κ] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (x : κ → Cb l) : ∃ (m : ℕ) (x' : κ → OCb l), ∀ j,
      algebraMap (OCb l) (Cb l) π ^ m * x j = algebraMap (OCb l) (Cb l) (x' j) := by
  choose n y hy using fun j => exists_clear hπ (x j)
  refine ⟨∑ j, n j, fun j => π ^ (∑ i, n i - n j) * y j, fun j => ?_⟩
  have hle : n j ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  rw [map_mul, ← hy j, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem map_constantCoeff_surj {F : Type} [CommRing F] (a : F⟦X⟧) :
    ∃ s : (WittVector l F)⟦X⟧, PowerSeries.map (WittVector.constantCoeff (p := l) (R := F)) s = a :=
  ⟨PowerSeries.mk fun n => WittVector.teichmuller l (PowerSeries.coeff n a), by
    ext n
    simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

end GlobalTheory.BSP.TwoCopy

namespace GlobalTheory.BSP.TwoCopy

theorem mem_reduction_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) →
    (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T),
      (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) →
    ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk κ _ x hfix hφ
  obtain ⟨ek, prA, hek, hinj, hpr, hpr1⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨hoe, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨-, -, -, h0, -, hc, -⟩ := _root_.GlobalTheory.BSP.AinfDiv.main l K bk
  have hH : IsHausdorff (Ideal.span {bk.flat}) (OCb l) := hc.toIsHausdorff
  have hX : ek X = bk.flat := by
    have := hek X
    rwa [PowerSeries.map_X, bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  obtain ⟨m, x', hx'⟩ := exists_clear_family hH x
  letI : Algebra (Fq l bk.a)⟦X⟧ (OCb l) := ek.toAlgebra
  have halg : ∀ a, algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a = ek a := fun _ => rfl
  haveI : Module.IsTorsionFree (Fq l bk.a)⟦X⟧ (OCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  let pr : OCb l →ₗ[(Fq l bk.a)⟦X⟧] (Fq l bk.a)⟦X⟧ :=
    { toFun := prA
      map_add' := prA.map_add
      map_smul' := fun a y => by rw [Algebra.smul_def, halg, hpr, RingHom.id_apply, smul_eq_mul] }
  have hEq : ∀ (T : Type) [CommRing T] (i₁ i₂ : OCb l →+* T),
      (∀ a, i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = i₂ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      IsUnit (i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x' j) - i₂ (x' j) = ∑ i, (i₁ (x' i) - i₂ (x' i)) ^ l * c i j := by
    intro T _ i₁ i₂ hag hu
    have hag' : ∀ a, i₁ (ek a) = i₂ (ek a) := hag
    rw [halg, hX] at hu
    have hf : i₁ bk.flat = i₂ bk.flat := by rw [← hX]; exact hag' X
    obtain ⟨j₁, hj₁⟩ := exists_ext hH i₁ hu
    obtain ⟨j₂, hj₂⟩ := exists_ext hH i₂ (hf ▸ hu)
    have hOE : ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), j₁ y = j₂ y := by
      intro y hy
      obtain ⟨n, s, hs⟩ := (hoe y).1 hy
      have hs' : i₁ ((bk.ev s).coeff 0) = i₂ ((bk.ev s).coeff 0) := by rw [← hek s]; exact hag' _
      have e1 := congrArg j₁ hs
      have e2 := congrArg j₂ hs
      rw [map_mul, map_pow, hj₁, hj₁, hs'] at e1
      rw [map_mul, map_pow, hj₂, hj₂, ← hf] at e2
      exact (hu.pow n).mul_left_cancel (e1.trans e2.symm)
    obtain ⟨c, hc'⟩ := hφ T j₁ j₂ hOE
    obtain ⟨υ, hυ⟩ := hu
    refine ⟨fun i j => c i j * (υ : T) ^ m * ((υ⁻¹ : Tˣ) : T) ^ (m * l), fun j => ?_⟩
    have hx1 : ∀ i, i₁ (x' i) = (υ : T) ^ m * j₁ (x i) := fun i => by
      rw [← hj₁, ← hx' i, map_mul, map_pow, hj₁, ← hυ]
    have hx2 : ∀ i, i₂ (x' i) = (υ : T) ^ m * j₂ (x i) := fun i => by
      rw [← hj₂, ← hx' i, map_mul, map_pow, hj₂, ← hf, ← hυ]
    have hinv : (υ : T) ^ (m * l) * ((υ⁻¹ : Tˣ) : T) ^ (m * l) = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    simp only [hx1, hx2]
    rw [← mul_sub, hc' j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, mul_pow, ← pow_mul]
    linear_combination (-((υ : T) ^ m * (j₁ (x i) - j₂ (x i)) ^ l * c i j)) * hinv
  have hPts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (ψ ψ' : OCb l →+* O), ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X) ≠ 0 →
      ¬ IsUnit (ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      IsAdicComplete (Ideal.span {ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)}) O →
      (∀ a, ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = ψ' (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      ∀ j, ψ (x' j) = ψ' (x' j) := by
    intro O _ _ _ _ _ ψ ψ' h1 h2 h3 hag j
    rw [halg, hX] at h1 h2 h3
    have hag' : ∀ a, ψ (ek a) = ψ' (ek a) := hag
    obtain ⟨g, hg, hψ⟩ := _root_.GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree l K bk O ψ h1 h2 h3 ψ' (fun s => by rw [← hek s]; exact hag' _)
    have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
    rw [hψ]
    congr 1
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← galTilt_apply, ← autCb_alg, ← hx' j, map_mul, map_pow, autCb_alg, hfix g hg j, galTilt_apply, hg']
  have hnz : algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X ∈ nonZeroDivisors (OCb l) := by
    rw [halg, hX]; exact mem_nonZeroDivisors_of_ne_zero h0
  have hHX : IsHausdorff (Ideal.span {algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X}) (OCb l) := by
    rw [halg, hX]; exact hH
  have key := _root_.GlobalTheory.descent_of_points_killed l (Fq l bk.a)⟦X⟧ (OCb l) X pr (CharP.cast_eq_zero _ _) hnz hHX κ x' hEq hPts hpr1
  intro j
  obtain ⟨s, hs⟩ := map_constantCoeff_surj (l := l) (prA (x' j))
  refine (hoe (x j)).2 ⟨m, s, ?_⟩
  rw [hx' j, ← hek s, hs]
  exact congrArg _ (key j)

end GlobalTheory.BSP.TwoCopy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobCoord

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem frob_mem_invL_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) : frob K l f ∈ invL l (S O K e) :=
  frob_mem_invL l (fun _ h => frob_mem_S l h) hf

theorem iSl_frob (ϖ : PiSys l e) (f : invL l (S O K e)) :
    ϖ.iSl O K ⟨frob K l f, frob_mem_invL_S f.2⟩ = frobOB l O (ϖ.iSl O K f) := by
  let F : invL l (S O K e) →+* invL l (S O K e) :=
    (frob K l).toRingHom.restrict _ _ fun _ h => frob_mem_invL_S h
  have key : (ϖ.iSl O K).toRingHom.comp F = (frobOB l O).toRingHom.comp (ϖ.iSl O K).toRingHom := by
    have hS : ∀ (x : S O K e) (h : frob K l (x : K⟦X⟧) ∈ invL l (S O K e)) (h' : (x : K⟦X⟧) ∈ invL l (S O K e)),
        ϖ.iSl O K ⟨frob K l x, h⟩ = frobOB l O (ϖ.iSl O K ⟨x, h'⟩) := fun x h h' => by
      rw [ϖ.iSl_of_mem O K (frob_mem_S l x.2) h, ϖ.iSl_of_mem O K x.2 h', ϖ.iS_frob O K x, frobOB_toOB]
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) ?_
    ext x
    exact hS x _ _
  exact RingHom.congr_fun key f

theorem frobOB_idem (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    frobOB l O (idem (constB t) τ) = idem (constB t) (τ + 1) := by
  change frobOB l O (toOB l O (toOCr l O (idem (constA t) τ))) = toOB l O (toOCr l O (idem (constA t) (τ + 1)))
  rw [frobOB_toOB, frobOCr_toOCr, frobOA_idem]

theorem iB_frob (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ZMod a → invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨frob K l (g (τ - 1)), frob_mem_invL_S (g (τ - 1)).2⟩) = frobOB l O (ϖ.iB t K g) :=
  (map_glue (frobOB l O).toRingHom 1 (frobOB_idem t) fun τ => (iSl_frob ϖ (g (τ - 1))).symm).symm

theorem iB_of_A (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (F : ZMod a → A O K)
    (h : ∀ τ, (F τ : K⟦X⟧) ∈ invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨F τ, h τ⟩) = toB l O (ϖ.iTot t K F) :=
  (ϖ.iB_of_mem t K fun τ => ⟨F τ, A_le_S l e (F τ).2⟩).trans (congrArg (toOB l O) (ϖ.iC_of_mem t K F))

theorem toBcris_phi (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ)
    (Y : Matrix ι ι (OA l O)) :
    (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) →
      ∀ m m' : P.MMl, m'.1 = P.phi m.1 →
        toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' =
          (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  intro hY m m' hm
  choose f hf hYf using hY
  set c := coordL P (invL l (S O K e)) m with hc
  set c' := coordL P (invL l (S O K e)) m' with hc'

  have step1 : ∀ i τ, frob K l (E K l e) ^ α * (c' i τ : K⟦X⟧) =
      ∑ j, (frobAc l (f i j) τ : K⟦X⟧) * frob K l (c j (τ - 1) : K⟦X⟧) := by
    intro i τ
    have h1 : (c' i τ : K⟦X⟧) = frob K l (m.1 (τ - 1) i) := by
      change (P.mxInv τ *ᵥ m'.1 τ) i = _
      rw [hm, PhiMod.phi_apply, Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
    have h2 : m.1 (τ - 1) i = ∑ j, P.mx (τ - 1) i j * (c j (τ - 1) : K⟦X⟧) := by
      rw [← mx_mulVec_coordL P _ m (τ - 1)]
      simp only [Matrix.mulVec, dotProduct, hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_frobAc, frobTot_apply, hf i j (τ - 1), map_mul, map_mul, map_pow, mul_assoc]

  let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
    fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
  let cF : ι → ZMod a → invL l (S O K e) :=
    fun j τ => ⟨frob K l (c j (τ - 1)), frob_mem_invL_S (c j (τ - 1)).2⟩
  have step2 : ∀ i, liftA (frobAc l fun _ => EIn l e (A O K)) ^ α * c' i =
      ∑ j, liftA (frobAc l (f i j)) * cF j := by
    intro i
    funext τ
    apply Subtype.ext
    simp only [liftA, cF, Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AddSubmonoidClass.coe_finsetSum]
    exact step1 i τ
  ext i
  have h3 := congrArg (ϖ.iB t K) (step2 i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, map_sum] at h3
  simp only [Finset.sum_congr rfl fun j _ => map_mul (ϖ.iB t K) (liftA (frobAc l (f i j))) (cF j)] at h3
  simp only [liftA, iB_of_A, cF, iB_frob, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
  rw [Pi.smul_apply, smul_eq_mul, toBcris_apply, ← hc', h3]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hYf, toBcris_apply, ← hc]

end GlobalTheory.BKGal.FrobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTheoremAllPowersOfSelmerSupLattice
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwExportSup

theorem heckeLaws_of_range (D : D7) (hC : HkComm D) (hO : OffRange D) : HeckeLaws D.nexp := by
  intro i hi
  refine ⟨fun j b k P k' P' h h' => ?_, (hO i hi).2⟩
  by_cases hj : j ∈ Finset.Icc 1 D.R.m
  · exact (hC i hi j hj b k P k' P' h h').eq
  · haveI := (hO i hi).1 j hj b
    exact LinearMap.ext fun x => Subsingleton.elim _ _

theorem twistTheorem_allPowers_of_selmer_supLattice :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), ThmS (BlochKatoReduction.bk0 D) → ResidualBoundOddPrimes (BlochKatoReduction.bk0 D) → ThmC (BlochKatoReduction.bk0 D) →
      BlochKatoReduction.Gen.AdmACD (BlochKatoReduction.bk0 D) N0 → DelUTie D.nexp → ThURel D.nexp → HkComm D → OffRange D → AllGood D.nexp →
      BlochKatoReduction.Gen.adm8 D.ntw D.nexp → SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
      IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → D.nexp.sig_all → HkSS D →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro D E N0 hS h103 hC hACD hTie hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS
  have hX : GaloisSideTwistedSelmerAuxiliaryPrimes (BlochKatoReduction.bk0 D) :=
    GlobalTheory.TwSys.galois_twisted_selmer_auxprimes_of_matrix_and_bounds D D.nd D.ntw (BlochKatoReduction.bk0 D) hS
      (GlobalTheory.SelDetLength.twisted_selmer_lengths_eq_determinant_valuation D D.nd D.ntw (BlochKatoReduction.bk0 D)) h103 hC
  have hP : PropABCD D.nexp :=
    GlobalTheory.TwistDet.propABCD_of_rel D D.nd D.ntw D.nexp hRel (heckeLaws_of_range D hHC hOff) hGood h8
  have hAB : admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 :=
    GlobalTheory.TwistChoiceAll.admissibleIndexBoundAllPowers_of_conditions D D.nd D.ntw (BlochKatoReduction.bk0 D) N0 hTie hP hX hACD
  have hInt : IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := _root_.GlobalTheory.IntSup.admInt_of_sup D E hG hFull hHk hU hT hComm
  have hAlg : IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := _root_.GlobalTheory.IdemAlg.admALG_of_commG D hComm
  exact GlobalTheory.exportAll_of_six_inputs D E N0 hAB hInt hAlg hT4 hL3 (_root_.GlobalTheory.EigRed.admT3_of_semisimple_good D E hInt hAlg hSig hSS)

end GlobalTheory.TwExportSup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChange
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.WachKernel


set_option maxHeartbeats 1600000 in
theorem kernel_freeA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  have hexact : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) :=
    GlobalTheory.EtaleExact.DD_exact D HW F
      (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  obtain ⟨hinj, hex, -⟩ := hexact
  obtain ⟨hDVR, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := (HW l).W_proj K s LL h T₁
  set N₀ := (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) with hN₀
  haveI : Module.Free W.EE (W.DD T₀) := (W.DD_free T₀).1
  haveI : IsNoetherianRing ↥(OL LL) :=
    @PrincipalIdealRing.isNoetherianRing _ _ hDVR.toIsPrincipalIdealRing
  haveI : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI : Module.Finite (AA K LL) ↥(W.N T₁) := Module.Finite.iff_fg.mpr (W.N_fg T₁)
  have hfin : Module.Finite (AA K LL) ↥N₀ := by
    let g : ↥N₀ →ₗ[AA K LL] ↥(W.N T₁) :=
      ((W.map ι).restrictScalars (AA K LL)).restrict (fun x hx => hx)
    haveI : IsNoetherian (AA K LL) ↥(W.N T₁) := isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective g fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab))
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hX : IsSMulRegular ↥N₀ (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) := by
    intro x y hxy
    have h1 : (letπ : AA K LL) • (x : W.DD T₀) = (letπ : AA K LL) • (y : W.DD T₀) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T₀)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  have hreg : ∀ x y : ↥N₀,
      (fun _ => C ((l : ℕ) : ↥(OL LL)) : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • x =
        (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • y →
      ∃ z : ↥N₀, x = (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • z := by
    intro x y hxy
    have hinj : Function.Injective (W.map ι) := hinj
    have hex : Function.Exact (W.map ι) (W.map π) := hex
    let mA := (W.map ι).restrictScalars (AA K LL)
    let x' : ↥(W.N T₁) := ⟨mA x, x.2⟩
    let y' : ↥(W.N T₁) := ⟨mA y, y.2⟩
    have hxy' : (fun _ => C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' = (fun _ => X : AA K LL) • y' := by
      apply Subtype.ext
      have := congrArg (fun w : ↥N₀ => mA (w : W.DD T₀)) hxy
      simpa only [Submodule.coe_smul, map_smul] using this
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @GlobalTheory.WachFree.mem_X_smul_of_projective ℤ_[l] ↥(W.N T₁) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x' y' (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x' =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y'
        rw [e1, e2]
        exact hxy')
    change x' = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    have hz' : mA x = (fun _ => X : AA K LL) • (z : W.DD T₁) := congrArg Subtype.val hz
    have hπz : W.map π (z : W.DD T₁) = 0 := by
      have h0 : W.map π (mA x) = 0 := (hex _).mpr ⟨(x : W.DD T₀), rfl⟩
      rw [hz'] at h0
      have h0' : (letπ : AA K LL) • W.map π (z : W.DD T₁) = (letπ : AA K LL) • 0 := by
        rw [smul_zero]
        have : W.map π ((letπ : AA K LL) • (z : W.DD T₁)) = (letπ : AA K LL) • W.map π (z : W.DD T₁) :=
          ((W.map π).restrictScalars (AA K LL)).map_smul _ _
        rw [← this]
        exact h0
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (0 : W.DD T₂)] at h0'
      exact W.EE_π.smul_left_cancel.mp h0'
    obtain ⟨w, hw⟩ := (hex (z : W.DD T₁)).mp hπz
    have hwN : w ∈ N₀ := by
      show W.map ι w ∈ W.N T₁
      rw [hw]
      exact z.2
    refine ⟨⟨w, hwN⟩, Subtype.ext (hinj ?_)⟩
    change mA x = W.map ι ((fun _ => X : AA K LL) • w)
    rw [hz', ← hw]
    exact (mA.map_smul _ _).symm
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥N₀) (E := W.EE) (D := W.DD T₀) W.EE_inj N₀.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hreg
  refine ⟨Module.finrank W.EE (W.DD T₀), fun j => (b j : W.DD T₀), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_, ?_⟩
  · have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  · intro a ha
    have hx' : (⟨x, hx⟩ : ↥N₀) = ∑ j, a j • b j :=
      Subtype.ext (by simpa only [Submodule.coe_sum, Submodule.coe_smul] using ha)
    funext j
    rw [hx', b.repr_sum_self]

end GlobalTheory.WachKernel
end

