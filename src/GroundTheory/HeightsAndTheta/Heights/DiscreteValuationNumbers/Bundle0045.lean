module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace FlagLineSectionProof

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F] {M : ℕ}

theorem chartMon_not_mem {W : Ideal (MRing (bundleIdx ι M) F)} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W) (α : K → ℕ) :
    chartMon F M c α ∉ W := by
  unfold chartMon
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, _, hk⟩
  exact hc k (hW.mem_of_pow_mem _ hk)

end FlagLineSectionProof


open FlagLineSectionProof in
theorem FlagLineSection.proof : FlagLineSection.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy _ N E _ _ B w b hB M a φ hφ Φ _ _ t ht h0
  have hXn : ∀ l : Fin M, projMap F y w φ (truncCoord t 1) (X ⟨none, l⟩) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l (w ⟨0, h0⟩))) * X none := by
    intro l
    rw [projMap_X_none, sum_truncCoord_one t h0]
  have ht0 : t ⟨0, h0⟩ ≠ 0 := fun h => ht.transcendental ⟨0, h0⟩ (h ▸ isAlgebraic_zero)

  have hyne : ∀ k (i : ι k), (X ⟨k, i⟩ : MRing ι F) ∉ pointIdeal F y → y ⟨k, i⟩ ≠ 0 := by
    intro k i hX h
    apply hX
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h]
  choose c0 hc0 using hy.relevant
  have live0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => hyne k _ (hc0 k)
  have hs0 := segreVec_ne_zero_of_live live0
  obtain ⟨hξ0, v0, -, hsum0⟩ := chart_data y B w b hB a φ hφ c0 hs0 h0
  obtain ⟨l0, hl0⟩ : ∃ l0, φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hsum0
  have hu0 : φ l0 (w ⟨0, h0⟩) ≠ 0 := left_ne_zero_of_mul hl0
  obtain ⟨n0, A0, hA0⟩ := exists_chartForm (M := M) y w φ (truncCoord t 1) c0 hs0 (hξ0 l0)
  obtain ⟨p, q, hpq⟩ : ∃ p q : K → ℕ, ∀ k, (p k : ℤ) - q k = -(b ⟨0, h0⟩ k - a k) - n0 :=
    ⟨fun k => (-(b ⟨0, h0⟩ k - a k) - n0).toNat, fun k => (-(-(b ⟨0, h0⟩ k - a k) - n0)).toNat,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hfval : projMap F y w φ (truncCoord t 1) (X ⟨none, l0⟩ * chartMon F M c0 q) =
      C (t ⟨0, h0⟩ * algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩))) * X none *
        (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ q k)) * tMon q) := by
    rw [map_mul, hXn, projMap_chartMon]
  have hgval : projMap F y w φ (truncCoord t 1) (A0 * chartMon F M c0 p) =
      C (algebraMap Ω Φ (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0)) *
        tMon (fun _ => n0) * (C (algebraMap Ω Φ (∏ k, y ⟨k, c0 k⟩ ^ p k)) * tMon p) := by
    rw [map_mul, hA0.2, projMap_chartMon]
  have hprod0 : ∀ r : K → ℕ, ∏ k, y ⟨k, c0 k⟩ ^ r k ≠ 0 :=
    fun r => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (live0 k)
  refine ⟨Pi.single none 1 + liftN q, liftN (fun _ => n0) + liftN p,
    X ⟨none, l0⟩ * chartMon F M c0 q, A0 * chartMon F M c0 p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isMultiHomog_X_none l0).mul (isMultiHomog_chartMon c0 q)
  · exact hA0.1.mul (isMultiHomog_chartMon c0 p)
  · rw [mem_projIdeal_iff, hfval]
    refine mul_ne_zero (mul_ne_zero ?_ (X_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero q))
    · rw [Ne, C_eq_zero]
      exact mul_ne_zero ht0 ((map_ne_zero _).mpr hu0)
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 q)
  · rw [mem_projIdeal_iff, hgval]
    refine mul_ne_zero (mul_ne_zero ?_ (tMon_ne_zero _)) (mul_ne_zero ?_ (tMon_ne_zero p))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (mul_ne_zero hl0 (pow_ne_zero _ hs0))
    · rw [Ne, C_eq_zero]
      exact (map_ne_zero _).mpr (hprod0 p)
  · funext o
    cases o with
    | none => simp [liftN, zetaDeg, liftDeg]
    | some k =>
      have := hpq k
      simp [liftN, zetaDeg, liftDeg]
      linarith
  · funext W
    show divCycle _ _ W - divCycle _ _ W = 0
    by_cases hW : W.IsPrime ∧ projIdeal F y w φ (truncCoord t 1) ≤ W ∧ IsRelevant W
    · obtain ⟨hWp, hPW, hWrel⟩ := hW
      choose cc hcc using fun k => hWrel (some k)
      let c : ∀ k, ι k := cc
      have hcW : ∀ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ∉ W := hcc
      obtain ⟨l1, hl1⟩ : ∃ l1 : Fin M, (X ⟨none, l1⟩ : MRing (bundleIdx ι M) F) ∉ W := hWrel none
      have live : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
        intro k h
        apply hcW k
        apply hPW
        rw [mem_projIdeal_iff, projMap_X_some, h, map_zero, C_0, zero_mul]
      have hs := segreVec_ne_zero_of_live live
      obtain ⟨hξ, vc, hvc, hsumc⟩ := chart_data y B w b hB a φ hφ c hs h0
      obtain ⟨nξ, hnξ⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hξ
      obtain ⟨nv, hnv⟩ := exists_chartForm_family (M := M) y w φ (truncCoord t 1) c hs _ hvc
      set m := nξ + nv with hm
      choose Ξ hΞ using hnξ m (by omega)
      choose V hV using hnv m (by omega)
      have htm : (tMon (fun _ : K => m + m) : MvPolynomial (Option K) Φ) =
          tMon (fun _ => m) * tMon (fun _ => m) := tMon_add (fun _ => m) (fun _ => m)
      have hR0 : ∑ l, V l * Ξ l - chartMon F M c (fun _ => m + m) ∈ projIdeal F y w φ (truncCoord t 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [mem_projIdeal_iff, map_sub, map_sum, projMap_chartMon, htm, sub_eq_zero]
        have e1 : ∀ l, projMap F y w φ (truncCoord t 1) (V l * Ξ l) =
            C (algebraMap Ω Φ (vc l * (φ l (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a)))) *
              (C (algebraMap Ω Φ (segreVec y c ^ (m + m))) * (tMon (fun _ => m) * tMon (fun _ => m))) := by
          intro l
          rw [map_mul, (hV l).2, (hΞ l).2]
          simp only [map_mul, map_pow, pow_add]
          ring
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.sum_mul, ← map_sum, ← map_sum, hsumc,
          map_one, map_one, one_mul]
        simp [segreVec, Finset.prod_pow]
      have hS : chartMon F M c (fun _ => m + m) ∉ W := chartMon_not_mem hcW _
      obtain ⟨l2, hl2⟩ : ∃ l2, Ξ l2 ∉ W := by
        by_contra hcon
        push Not at hcon
        have hsumW : ∑ l, V l * Ξ l ∈ W := Ideal.sum_mem _ fun l _ => W.mul_mem_left _ (hcon l)
        apply hS
        have := W.sub_mem hsumW (hPW hR0)
        rwa [sub_sub_cancel] at this
      have hR1 : X ⟨none, l1⟩ * Ξ l2 - X ⟨none, l2⟩ * Ξ l1 ∈ projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul, map_mul, hXn, hXn, (hΞ l2).2, (hΞ l1).2, sub_eq_zero]
        simp only [map_mul]
        ring
      have h12 : X ⟨none, l1⟩ * Ξ l2 ∉ W := fun h => (hWp.mem_or_mem h).elim hl1 hl2
      have h21 : X ⟨none, l2⟩ * Ξ l1 ∉ W := fun h => h12 (by
        have := W.add_mem (hPW hR1) h
        rwa [sub_add_cancel] at this)
      have hx2 : (X ⟨none, l2⟩ : MRing (bundleIdx ι M) F) ∉ W := fun h => h21 (W.mul_mem_right _ h)
      obtain ⟨α, β, hαβ⟩ : ∃ α β : K → ℕ, ∀ k, (β k : ℤ) - α k = m + (b ⟨0, h0⟩ k - a k) :=
        ⟨fun k => (-(m + (b ⟨0, h0⟩ k - a k))).toNat, fun k => (m + (b ⟨0, h0⟩ k - a k)).toNat,
          fun k => Int.toNat_sub_toNat_neg _⟩
      have hne1 : Ξ l2 * chartMon F M c α ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hl2 (chartMon_not_mem hcW α)
      have hne2 : X ⟨none, l2⟩ * chartMon F M c β ∉ W :=
        fun h => (hWp.mem_or_mem h).elim hx2 (chartMon_not_mem hcW β)
      have hT : (tMon (fun _ => m) * tMon α * tMon q : MvPolynomial (Option K) Φ) =
          tMon β * tMon (fun _ => n0) * tMon p := by
        rw [← tMon_add, ← tMon_add, ← tMon_add, ← tMon_add]
        congr 1
        funext k
        have h1 := hαβ k
        have h2 := hpq k
        simp only [Pi.add_apply]
        omega
      have hc1 : chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m * ∏ k, y ⟨k, c k⟩ ^ α k =
          ∏ k, y ⟨k, c k⟩ ^ β k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live, ← chartZ_add live]
        congr 1
        funext k
        have h1 := hαβ k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hc0 : chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0 * ∏ k, y ⟨k, c0 k⟩ ^ p k =
          ∏ k, y ⟨k, c0 k⟩ ^ q k := by
        rw [segreVec_pow, ← chartZ_natCast, ← chartZ_natCast, ← chartZ_add live0, ← chartZ_add live0]
        congr 1
        funext k
        have h2 := hpq k
        simp only [Pi.add_apply, Pi.sub_apply]
        omega
      have hΩ : φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) * segreVec y c ^ m *
            (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c0 k⟩ ^ q k) =
          φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
            (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
            (∏ k, y ⟨k, c0 k⟩ ^ p k) := by
        rw [← hc1, ← hc0]
        ring
      have hcross : (Ξ l2 * chartMon F M c α) * (X ⟨none, l0⟩ * chartMon F M c0 q) -
          (X ⟨none, l2⟩ * chartMon F M c β) * (A0 * chartMon F M c0 p) ∈
            projIdeal F y w φ (truncCoord t 1) := by
        rw [mem_projIdeal_iff, map_sub, map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2 * _),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩ * _), hfval, hgval,
          map_mul (projMap F y w φ (truncCoord t 1)) (Ξ l2),
          map_mul (projMap F y w φ (truncCoord t 1)) (X ⟨none, l2⟩), (hΞ l2).2, hXn, projMap_chartMon, projMap_chartMon, sub_eq_zero]
        calc _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * chartZ y c (b ⟨0, h0⟩ - a) *
                segreVec y c ^ m * (∏ k, y ⟨k, c k⟩ ^ α k) * φ l0 (w ⟨0, h0⟩) *
                (∏ k, y ⟨k, c0 k⟩ ^ q k))) * X none * (tMon (fun _ => m) * tMon α * tMon q) := by
              simp only [map_mul]
              ring
          _ = C (t ⟨0, h0⟩) * C (algebraMap Ω Φ (φ l2 (w ⟨0, h0⟩) * (∏ k, y ⟨k, c k⟩ ^ β k) *
                (φ l0 (w ⟨0, h0⟩) * chartZ y c0 (b ⟨0, h0⟩ - a) * segreVec y c0 ^ n0) *
                (∏ k, y ⟨k, c0 k⟩ ^ p k))) * X none * (tMon β * tMon (fun _ => n0) * tMon p) := by
              rw [hΩ, hT]
          _ = _ := by
              simp only [map_mul]
              ring
      rw [divCycle_eq_of_mul_sub_mem hne1 hne2 hcross, sub_self]
    · have hz : ∀ h, divCycle (projIdeal F y w φ (truncCoord t 1)) h W = 0 := by
        intro h
        by_contra hne
        exact hW (le_and_isRelevant_of_divCycle_ne_zero hne)
      rw [hz, hz, sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLengthMapIdealLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open IsLocalRing

theorem LengthMapIdealLe.proof : LengthMapIdealLe.Statement.{u} := by
  intro C D _ _ _ φ hφ
  suffices key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n →
      Module.length D (D ⧸ I.map φ) ≤ n by
    intro I
    cases h : Module.length C (C ⧸ I) with
    | top => exact le_top
    | coe n => exact key n I h
  intro n
  induction n with
  | zero =>
    intro I hI
    have hs : Subsingleton (C ⧸ I) := Module.length_eq_zero_iff.mp (by exact_mod_cast hI)
    have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    subst hItop
    rw [Ideal.map_top]
    have : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro I hI
    have hfin : IsFiniteLength C (C ⧸ I) :=
      Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)
    have : IsArtinian C (C ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have : Nontrivial (C ⧸ I) :=
      Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule C (C ⧸ I)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot
    have hNs : IsSimpleModule C N := isSimpleModule_iff_isAtom.mpr hN

    have hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one (R := C) (M := N), hI] at hlen
    have hq : Module.length C ((C ⧸ I) ⧸ N) = n := by
      have hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top] at hlen
        exact ENat.natCast_ne_top _ hlen
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hk] at hlen ⊢
      norm_cast at hlen ⊢
      omega

    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN.1
    have hspan : Submodule.span C {v} = N :=
      (hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left
        (by simpa using hv0)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v

    set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def
    have hII' : I ≤ I' := by
      intro x hx
      show Submodule.mkQ I x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    have hI'N : Submodule.map (Submodule.mkQ I) I' = N :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N
    have hlenI' : Module.length C (C ⧸ I') = n := by
      rw [← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]
    have ih' := ih I' hlenI'

    set m : Ideal C := Module.annihilator C N
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmc : ∀ x ∈ m, x * c ∈ I := by
      intro x hx
      have h1 := Module.mem_annihilator.mp hx ⟨_, hvN⟩
      have h2 : x • (Ideal.Quotient.mk I c) = 0 := congrArg Subtype.val h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      simpa [Algebra.smul_def] using h2

    have hI'le : I' ≤ I ⊔ Ideal.span {c} := by
      intro x hx
      have hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c} := hspan ▸ hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
      have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c) := by
        rw [map_mul]
        simpa [Algebra.smul_def] using ha.symm
      have hd : x - a * c ∈ I := Ideal.Quotient.eq.mp hxa
      rw [show x = (x - a * c) + a * c by ring]
      exact Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))

    set J : Ideal D := I.map φ
    set J' : Ideal D := I'.map φ
    have hJJ' : J ≤ J' := Ideal.map_mono hII'
    have hJ'le : J' ≤ J ⊔ Ideal.span {φ c} := by
      calc J' ≤ (I ⊔ Ideal.span {c}).map φ := Ideal.map_mono hI'le
        _ = J ⊔ Ideal.span {φ c} := by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)
    set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'
    have hK : K ≤ Submodule.span D {w} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, q, hq', rfl⟩ := Submodule.mem_sup.mp (hJ'le hy)
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp,
        zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)
    have hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J') := by
      rw [Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]

    have hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem φ (hmc x hx)
    have hKle1 : Module.length D K ≤ 1 := by
      rcases hφ m hm with htop | hle
      · have hw : w = 0 := by
          have h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
            hmX (htop ▸ Submodule.mem_top)
          simpa using h1
        have hK0 : K = ⊥ := le_bot_iff.mp (hK.trans (by simp [hw]))
        rw [hK0, Module.length_bot]
        exact zero_le
      · have h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
          hle.trans hmX
        let f := (maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1
        have hrange : LinearMap.range f = Submodule.span D {w} := by
          rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
        have : IsSimpleModule D (D ⧸ maximalIdeal D) :=
          isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        calc Module.length D K ≤ Module.length D (Submodule.span D {w}) :=
              Module.length_le_of_injective (Submodule.inclusion hK) (Submodule.inclusion_injective hK)
          _ = Module.length D (LinearMap.range f) := by rw [hrange]
          _ ≤ Module.length D (D ⧸ maximalIdeal D) :=
              Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          _ = 1 := Module.length_eq_one _ _
    calc Module.length D (D ⧸ I.map φ) = Module.length D K + Module.length D (D ⧸ J') := hlenD
      _ ≤ 1 + n := add_le_add hKle1 ih'
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCycleSpanMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LocCycleSpanMul.mem_minimalPrimes_iff {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W

theorem LocCycleSpanMul.proof : LocCycleSpanMul.Statement := by
  intro A _ _ _ x y hx hy W
  by_cases hP : W.IsPrime ∧ W.height = 1
  · obtain ⟨hp, h1⟩ := hP
    have key : ∀ z : A, z ≠ 0 →
        locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧
          locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤ := by
      intro z hz
      by_cases hzW : z ∈ W
      · have hm : W ∈ (Ideal.span {z}).minimalPrimes :=
          (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩
        refine ⟨?_, locLen_ne_top hm⟩
        unfold locCycle
        rw [dite_eq_left hm]
        rfl
      · have hm : W ∉ (Ideal.span {z}).minimalPrimes := fun h =>
          hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2
        have h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0 := by
          have := locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW
          rwa [bot_sup_eq] at this
        refine ⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩
        unfold locCycle
        rw [dite_eq_right hm, h0]
        simp
    obtain ⟨ex, fx⟩ := key x hx
    obtain ⟨ey, fy⟩ := key y hy
    obtain ⟨exy, -⟩ := key (x * y) (mul_ne_zero hx hy)
    have hmul := locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x)
      (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩
    rw [bot_sup_eq, bot_sup_eq, bot_sup_eq] at hmul
    rw [exy, ex, ey, hmul, ENat.toNat_add fy fx]
    push_cast
    ring
  · have hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0 := by
      intro z hz
      unfold locCycle
      rw [dite_eq_right]
      intro hm
      have h := (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm
      exact hP ⟨h.1, h.2.1⟩
    rw [hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimesSpanSingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MinimalPrimesSpanSingleton.proof : MinimalPrimesSpanSingleton.Statement.{u} := by
  intro A _ _ _ x hx W
  constructor
  · intro hW
    have hWp : W.IsPrime := hW.isPrime
    have hxW : x ∈ W := hW.1.2 (Ideal.mem_span_singleton_self x)
    refine ⟨hWp, ?_, hxW⟩
    have hle : W.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW
    have hne : W.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      rw [hbot, Ideal.mem_bot] at hxW
      exact hx hxW
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  · rintro ⟨hWp, hh, hxW⟩
    refine ⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩
    rintro Q ⟨hQp, hxQ⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))
    have hfin : W.FiniteHeight := W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
    have hQh : Q.height < 1 := hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hQ0 : Q.height = 0 := Order.lt_one_iff.mp hQh
    rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
    have hx0 : x ∈ (⊥ : Ideal A) := hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ
    exact hx ((Ideal.mem_bot).mp hx0)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

