module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import ReciprocityTheory.DualLattices.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_injective_lift_field {R S K : Type} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hK : IsField K) (g : R →+* K) (hg : Function.Injective g)
    (hM : ∀ y ∈ M, y ≠ 0) :
    ∃ ι : S →+* K, (∀ x : R, ι (algebraMap R S x) = g x) ∧ Function.Injective ι := by
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    have h : g y ≠ 0 := fun h => hM y y.2 (hg (by rw [h, map_zero]))
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]
  · intro h
    rw [hg h]

theorem algebraMap_ainf_acris_eq {l : ℕ} [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem algebraMap_ainf_acris_ne_zero_pt {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l)
    (hj : IsCrisP j) (x : Per.Ainf l) (hx0 : x ≠ 0) : algebraMap (Per.Ainf l) (Per.Acris l) x ≠ 0 := by
  obtain ⟨hd, -, hi⟩ := _root_.GlobalTheory.MemLoc.ainf_isDomain_and_injective l
  intro h'
  apply hx0
  have h1 := hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
  rw [← algebraMap_ainf_acris_eq] at h1
  rw [h', map_zero] at h1
  have h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0 :=
    _root_.GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective l (by rw [map_zero]; exact h1.symm)
  exact hi (by rw [map_zero]; exact h2)

theorem pow_root_ne_zero {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (hne : e ≠ 1) (n : ℕ) :
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n ≠ 0 := by
  obtain ⟨hd, -, -⟩ := _root_.GlobalTheory.MemLoc.ainf_isDomain_and_injective l
  rw [← map_pow]
  refine algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)
  exact GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])

theorem exists_iota_cris_dR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j →
    ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  intro l _ j hj
  obtain ⟨-, hi, hK, -⟩ := _root_.GlobalTheory.MemLoc.BdRField.bdR_isField l
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI := GlobalTheory.CrisLoc.bcris_away l e he hne
  refine exists_injective_lift_field
    (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK
    ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (_root_.GlobalTheory.MemLoc.crisP_injective l j hj)) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_root_ne_zero j hj e hne n

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
section
open IsLocalRing

namespace GlobalTheory

theorem finite_integralClosure_of_isLocalization {R S L : Type*} [CommRing R] [CommRing S]
    [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R L)
  let f : integralClosure R L → integralClosure S L := fun z => ⟨z, IsIntegral.tower_top z.2⟩
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M (Rₘ := S) (y : L) y.2
  have key : ∀ z ∈ Submodule.span R (s : Set (integralClosure R L)),
      f z ∈ Submodule.span S (↑(s.image f) : Set (integralClosure S L)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem f hx))
    | zero =>
      have : f 0 = 0 := rfl
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : f (x + y) = f x + f y := rfl
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : f (a • x) = algebraMap R S a • f x := by
        apply Subtype.ext
        change a • (x : L) = algebraMap R S a • (x : L)
        rw [algebraMap_smul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  have hz : (⟨m • (y : L), hm⟩ : integralClosure R L) ∈ Submodule.span R (s : Set _) :=
    hs ▸ Submodule.mem_top
  have e : y = IsLocalization.mk' S (1 : R) m • f ⟨m • (y : L), hm⟩ := by
    apply Subtype.ext
    change (y : L) = IsLocalization.mk' S (1 : R) m • ((m : R) • (y : L))
    rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S L, ← mul_assoc,
      ← map_mul, IsLocalization.mk'_spec, map_one, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ hz)

theorem finite_integralClosure_of_essFiniteType_int :
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D],
      Module.Finite D (integralClosure D (FractionRing D)) := by
  intro D _ _ _
  obtain ⟨S₀, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ D).mp inferInstance
  let K := FractionRing D
  have hinj : Function.Injective (algebraMap S₀ D) := Subtype.val_injective
  haveI hfr : IsFractionRing S₀ K := by
    have h := IsLocalization.localization_localization_isLocalization_of_has_all_units M (nonZeroDivisors D) K
      (fun x hx => hx.mem_nonZeroDivisors)
    have e : (nonZeroDivisors D).comap (algebraMap S₀ D) = nonZeroDivisors S₀ := by
      ext x
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
      exact (map_eq_zero_iff _ hinj).not
    rw [e] at h
    exact h
  suffices h : Module.Finite S₀ (integralClosure S₀ K) from
    finite_integralClosure_of_isLocalization M
  rcases CharP.char_is_prime_or_zero D (ringChar D) with hp | h0
  · haveI : Fact (ringChar D).Prime := ⟨hp⟩
    haveI : CharP D (ringChar D) := ringChar.charP D
    haveI : CharP S₀ (ringChar D) := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff D]⟩
    letI : Algebra (ZMod (ringChar D)) S₀ := (ZMod.castHom dvd_rfl S₀).toAlgebra
    haveI : Algebra.FiniteType (ZMod (ringChar D)) S₀ :=
      .of_restrictScalars_finiteType ℤ (ZMod (ringChar D)) S₀
    exact NormFin.finite_integralClosure_of_perfectField (ZMod (ringChar D)) S₀ K K
  · haveI : CharZero D := (CharP.ringChar_zero_iff_CharZero D).mp h0
    haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
    haveI : Algebra.EssFiniteType S₀ D := .of_isLocalization D M
    haveI : Algebra.EssFiniteType D K := .of_isLocalization K (nonZeroDivisors D)
    haveI : Algebra.EssFiniteType S₀ K := .comp S₀ D K
    exact GlobalTheory.finite_integralClosure_of_essFiniteType_field ℤ S₀ K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
section
open NumberField
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV

section Frames

variable {K : Type} [Field K] [NumberField K]


open Classical in
def frm {n : ℕ} (H : Matrix (Fin n) (Fin n) K) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun v => if (H.map v.embedding).PosDef then frameOf (H.map v.embedding) else 1

theorem frm_det {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : IsUnit (frm H v).det := by
  unfold frm
  split_ifs with h
  · exact (frameOfSpec _ _ h).1
  · simp

theorem frm_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    frm H v = frameOf (H.map v.embedding) := by
  unfold frm
  rw [if_pos h]

end Frames

section Coord

variable {K : Type} [Field K]

def rdx {a b : ℕ} (h : a = b) : (Fin b → K) ≃ₗ[K] (Fin a → K) := LinearEquiv.funCongrLeft K K (finCongr h)

theorem rdx_apply {a b : ℕ} (h : a = b) (x : Fin b → K) (i : Fin a) : rdx h x i = x (Fin.cast h i) := rfl

theorem rdx_refl {a : ℕ} (h : a = a) (x : Fin a → K) : rdx h x = x := by
  funext i
  rw [rdx_apply]
  rfl

end Coord

end GlobalTheory.AmbCrd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem theta_ker_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θ l) ∧ IsDomain (Per.Ainf l) ∧ ((l : ℕ) : Per.Ainf l) ≠ 0 ∧ ∀ e : Per.Fl l, IsEps e → RingHom.ker (Per.θ l) = Ideal.span {xi e} ∧ xi e ≠ 0 := by
  intro l _
  have hv := PadicComplexInt.integers l
  haveI : IsDomain (Per.Fl l) := PreTilt.isDomain _ _ _ hv l
  have hl : ((l : ℕ) : Per.Ainf l) ≠ 0 := fun h => by
    have h1 := congrArg (Per.θ l) h
    rw [map_natCast, map_zero] at h1
    exact GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h1)
  refine ⟨ReciprocityTheory.PGsh.Ainf.theta_surj l _ hv, inferInstance, hl, fun e he => ?_⟩
  have hε : IsPrimitiveRoot (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) l := by
    have h1 : (((frobeniusEquiv (Per.Fl l) l).symm e).untilt) ^ l = 1 := by
      rw [← map_pow, frobeniusEquiv_symm_pow_p]; exact he.1
    have h2 := he.2
    generalize ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = y at h1 h2 ⊢
    have h3 := IsPrimitiveRoot.orderOf y
    rwa [orderOf_eq_prime h1 h2] at h3
  refine ⟨ReciprocityTheory.PGsh.Ainf.ker_theta l _ hv e hε, fun h => ?_⟩
  exact one_ne_zero (ReciprocityTheory.PGsh.Ainf.xi_nzd l _ hv e hε 1 (by rw [one_mul]; exact h))

theorem tilt_facts : ∀ (l : ℕ) [Fact l.Prime], (∀ x : ℕ → Per.OC l, (∀ n, x (n + 1) ^ l = x n) → ∃ e : Per.Fl l, ∀ n, rootT e n = x n) ∧ (∀ e : Per.Fl l, (∀ n, rootT e n = 1) → e = 1) ∧ (∀ (e : Per.Fl l) (m n : ℕ), rootT (e ^ m) n = rootT e n ^ m) := by
  intro l _
  have key : ∀ (e : Per.Fl l) (n : ℕ), Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (rootT e n) =
      PreTilt.coeff n e := by
    intro e n
    rw [rootT, PreTilt.mk_untilt_eq_coeff_zero]
    exact PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n e |>.trans (by rw [zero_add])
  refine ⟨fun x hx => ?_, fun e he => ?_, fun e m n => ?_⟩
  · let e : Perfection (ModP (Per.OC l) l) l :=
      ⟨fun n => Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (x n), fun n => by
        rw [← map_pow, hx]⟩
    have hp : ∀ n k, x (n + k) ^ l ^ k = x n := by
      intro n k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, hx, ih]
    refine ⟨e, fun n => ?_⟩
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun k => ⟨x (n + k), ?_, ?_⟩
    · refine Eq.trans ?_ (PreTilt.coeff_iterate_frobeniusEquiv_symm (O := Per.OC l) k n e).symm
      rw [add_comm]; rfl
    · rw [hp]
  · refine Perfection.ext fun n => ?_
    have := key e n
    rw [he, map_one] at this
    exact this.symm.trans (map_one (PreTilt.coeff n)).symm
  · rw [rootT, rootT, ← map_pow]
    congr 1
    exact iterate_map_pow (frobeniusEquiv (Per.Fl l) l).symm.toRingHom n e m

theorem thetaP_facts : ∀ (l : ℕ) [Fact l.Prime], Function.Surjective (Per.θP l) ∧ RingHom.ker (Per.θP l) = Per.kerP l ∧ (∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l])) ∧ (∀ a : Per.AinfP l, Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) ∧ ∀ e : Per.Fl l, IsEps e → Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)} := by
  intro l _
  obtain ⟨hs, hdom, hl, hk⟩ := theta_ker_facts l
  have hle : Submonoid.powers ((l : ℕ) : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hl
  have hA : ∀ a : Per.Ainf l, Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = (Per.θ l a : ℂ_[l]) :=
    fun a => GlobalTheory.RingIface.fontaineTheta_algebraMap l a
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hsurj : ∀ y : Per.AinfP l, ∃ (n : ℕ) (a : Per.Ainf l),
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y => by
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    exact ⟨n, a, by rwa [map_natCast] at h⟩
  have hz : ∀ y : Per.AinfP l, Per.θP l y = 0 → ∃ (n : ℕ) (a : Per.Ainf l), Per.θ l a = 0 ∧
      y * ((l : ℕ) : Per.AinfP l) ^ n = algebraMap (Per.Ainf l) (Per.AinfP l) a := fun y hy => by
    obtain ⟨n, a, h⟩ := hsurj y
    refine ⟨n, a, Subtype.ext ?_, h⟩
    rw [← hA, ← h, map_mul, hy, zero_mul]
    rfl
  have hker : RingHom.ker (Per.θP l) = Per.kerP l := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l y (by rwa [pow_one]))
    obtain ⟨n, a, ha, h⟩ := hz y hy
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
    exact GlobalTheory.RingIface.alg_mem_kerP l ha
  refine ⟨fun x => ?_, hker, hA, fun a => ?_, IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
    IsLocalization.injective _ hle, fun e he => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖x * ((l : ℕ) : ℂ_[l]) ^ n‖ ≤ 1 := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (GlobalTheory.RingBasics.norm_p_lt (p := l))).const_mul ‖x‖
      rw [mul_zero] at h1
      obtain ⟨n, hn⟩ := (h1.eventually (eventually_le_nhds one_pos)).exists
      exact ⟨n, by rwa [norm_mul, norm_pow]⟩
    obtain ⟨a, ha⟩ := hs ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hn⟩
    obtain ⟨d, hd⟩ := (hu.pow n).exists_right_inv
    refine ⟨algebraMap _ _ a * d, ?_⟩
    have h2 := congrArg (Per.θP l) hd
    rw [map_mul, map_pow, map_natCast, map_one] at h2
    rw [map_mul, hA, ha, mul_assoc, h2, mul_one]
  · exact GlobalTheory.RingIface.thetaD_alg l a
  · obtain ⟨h1, -⟩ := hk e he
    refine le_antisymm (fun y hy => ?_) ?_
    · rw [← hker] at hy
      obtain ⟨n, a, ha, h⟩ := hz y hy
      rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h]
      have h2 : a ∈ Ideal.span {xi e} := h1 ▸ ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 h2
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, ← hker, RingHom.mem_ker, hA, Model.theta_xi he]
      rfl

end GlobalTheory.MemLoc
end

