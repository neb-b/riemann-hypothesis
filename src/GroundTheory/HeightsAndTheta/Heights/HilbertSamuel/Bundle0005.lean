module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology NNReal

theorem RootsBounded.continuous_aeval {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem RootsBounded.proof : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem RootsLiftToZeros.exists_extend {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ) (hker : RingHom.ker (algebraMap R A) ≤ RingHom.ker ev) :
    ∃ χ : A →+* ℂ, χ.comp (algebraMap R A) = ev :=
  _root_.UpperTheory.Reformulated.B.Qi28.exists_extend ev hker

theorem RootsLiftToZeros.proof : RootsLiftToZeros.Statement := by
  intro σ P e ℓ u G hint hG y t ht
  classical
  let A := MvPolynomial σ ℚ ⧸ P
  let α : Polynomial (MvPolynomial (Fin e) ℚ) →+* A :=
    (Ideal.Quotient.mk P).comp (Polynomial.eval₂RingHom (aeval ℓ).toRingHom u)
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ)) A := α.toAlgebra
  have hα : ∀ Q, algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A Q =
      Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) := fun _ => rfl
  have _ : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ)) A := by
    constructor
    intro a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hpm, hp⟩ := hint g
    refine ⟨p.map Polynomial.C, hpm.map _, ?_⟩
    have hc : (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A).comp Polynomial.C =
        (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom :=
      RingHom.ext fun r => by simp [hα]
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  let ev : Polynomial (MvPolynomial (Fin e) ℚ) →+* ℂ := Polynomial.eval₂RingHom (aeval y).toRingHom t
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) A) ≤ RingHom.ker ev := by
    intro Q hQ
    rw [RingHom.mem_ker, hα, Ideal.Quotient.eq_zero_iff_mem] at hQ
    obtain ⟨H, rfl⟩ := hG Q hQ
    rw [RingHom.mem_ker, map_mul]
    change Polynomial.eval₂ (aeval y).toRingHom t G * ev H = 0
    rw [ht, zero_mul]
  obtain ⟨ψ, hψ⟩ := RootsLiftToZeros.exists_extend ev hker
  let χ : MvPolynomial σ ℚ →+* ℂ := ψ.comp (Ideal.Quotient.mk P)
  have hχ : χ = (aeval fun i => χ (X i)).toRingHom :=
    MvPolynomial.ringHom_ext
      (fun r => RingHom.congr_fun (Subsingleton.elim (χ.comp C) ((aeval fun i => χ (X i)).toRingHom.comp C)) r)
      (fun i => by simp)
  have key : ∀ Q, χ (Q.eval₂ (aeval ℓ).toRingHom u) = ev Q := fun Q => RingHom.congr_fun hψ Q
  have hz : ∀ g, aeval (fun i => χ (X i)) g = χ g := fun g => (RingHom.congr_fun hχ g).symm
  refine ⟨fun i => χ (X i), fun g hg => ?_, funext fun j => ?_, ?_⟩
  · rw [hz]
    change ψ (Ideal.Quotient.mk P g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  · have := key (Polynomial.C (X j))
    simp only [Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at this
    rw [hz, this]
    simp [ev]
  · have := key Polynomial.X
    simp only [Polynomial.eval₂_X] at this
    rw [hz, this]
    simp [ev]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

theorem RootsNear.pow_card_le_norm_prod (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have h1 : ε ≤ ‖t₀ - a‖ := by
      rw [← dist_eq_norm, dist_comm]; exact h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)

theorem RootsNear.continuous_eval₂ {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  have : (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) =
      fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i)) := by
    funext y
    simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

theorem RootsNear.proof : RootsNear.Statement := by
  intro e G hG y₀ t₀ h0 ε hε
  have hpos : (0 : ℝ) < ε ^ G.natDegree := pow_pos hε _
  have ht := (RootsNear.continuous_eval₂ G t₀).tendsto y₀
  rw [h0] at ht
  filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy
  rw [Set.mem_preimage, mem_ball_zero_iff] at hy
  by_contra hno
  push Not at hno
  set p := G.map (aeval y).toRingHom with hp
  have hpm : p.Monic := hG.map _
  have hdeg : p.natDegree = G.natDegree := hG.natDegree_map _
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard
  have hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod := by
    rw [← Polynomial.eval_map, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hle := RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by
    have ha' : p.eval₂ (RingHom.id ℂ) a = 0 := by
      rw [Polynomial.eval₂_id]; exact (Polynomial.mem_roots hpm.ne_zero).1 ha
    have := hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')
    exact this)
  rw [hcard, hdeg, ← hev] at hle
  exact absurd hy (not_lt.2 hle)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

theorem UnitApprox.proof : UnitApprox.Statement := by
  intro F _ _ u hconj hsum
  classical
  let uw : InfinitePlace F → ℝ := fun w => u w.embedding
  have hu_mk : ∀ sg, u sg = uw (InfinitePlace.mk sg) := by
    intro sg
    rcases embedding_mk_eq sg with h | h
    · simp only [uw, h]
    · simp only [uw, h, hconj]
  have hsum' : ∑ w : InfinitePlace F, (mult w : ℝ) * uw w = 0 := by
    rw [← hsum, ← Finset.sum_fiberwise Finset.univ (fun sg => InfinitePlace.mk sg) u]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => uw w), Finset.sum_const, nsmul_eq_mul,
      card_filter_mk_eq]
    intro sg hsg
    rw [Finset.mem_filter] at hsg
    rw [hu_mk, hsg.2]
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card (InfinitePlace F) * R, fun n => ?_⟩
  let v : logSpace F := fun w => n * ((mult w.val : ℝ) * uw w.val)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, ?_⟩
  set ε := Additive.toMul x with hε
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  let e : InfinitePlace F → ℝ := fun w =>
    mult w * (Real.log (w ((ε : 𝓞 F) : F)) - n * uw w)
  have he_ne : ∀ w (hw : w ≠ w₀), |e w| ≤ R := by
    intro w hw
    have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) ⟨w, hw⟩
    rw [← hx] at h1
    have h2 : (logEmbedding F).toIntLinearMap x ⟨w, hw⟩
        = mult w * Real.log (w ((ε : 𝓞 F) : F)) := rfl
    rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
    have h3 : e w = -(v ⟨w, hw⟩ - mult w * Real.log (w ((ε : 𝓞 F) : F))) := by
      simp only [e, v]; ring
    rw [h3, abs_neg]
    rw [← hx] at hfr
    linarith
  have he_sum : ∑ w, e w = 0 := by
    have h := sum_mult_mul_log ε
    have h2 : ∑ w : InfinitePlace F, (mult w : ℝ) * (n * uw w)
        = n * ∑ w, (mult w : ℝ) * uw w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e, mul_sub, Finset.sum_sub_distrib, h2, hsum', mul_zero, sub_zero]
    exact h
  have he : ∀ w, |e w| ≤ Fintype.card (InfinitePlace F) * R := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ w₀)
      rw [he_sum] at h
      have h3 : e w₀ = -∑ w ∈ Finset.univ.erase w₀, e w := by linarith
      rw [h3, abs_neg]
      calc |∑ w ∈ Finset.univ.erase w₀, e w| ≤ ∑ w ∈ Finset.univ.erase w₀, |e w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ Finset.univ.erase w₀, R :=
            Finset.sum_le_sum fun w hw => he_ne w (Finset.ne_of_mem_erase hw)
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (he_ne w hw).trans (le_mul_of_one_le_left hR0 hcard)
  intro sg
  have hm : (1 : ℝ) ≤ mult (InfinitePlace.mk sg) := one_le_mult
  have h4 : |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ |e (InfinitePlace.mk sg)| := by
    simp only [e, abs_mul, hu_mk sg, InfinitePlace.apply, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hm
  exact h4.trans (he _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]


variable {ι}

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

end Cycle

section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexTaylor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix

noncomputable section

def ComplexTaylorTwo.Statement : Prop :=
  ∀ (D : ℕ) (ψ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), ContDiffAt ℝ 2 ψ y₀ →
    ∃ (a : Fin D → ℂ) (b : Matrix (Fin D) (Fin D) ℂ),
      (fun z : Fin D → ℂ => ψ (y₀ + z) - ψ y₀ - (a ⬝ᵥ z + z ⬝ᵥ (b *ᵥ z)).re -
          (z ⬝ᵥ (hessC ψ y₀ *ᵥ star z)).re) =o[𝓝 0] fun z => ‖z‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LeviLogFlat.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (P u : (J → ℂ) → ℝ) (z w : J → ℂ),
    ContDiffAt ℝ 2 P z → ContDiffAt ℝ 2 u z → 0 < P z → u z = 0 → fderiv ℝ u z w = 0 →
    fderiv ℝ u z (Complex.I • w) = 0 → leviForm u z w = 0 →
    leviForm (fun x => Real.log (P x + u x)) z w = leviForm (fun x => Real.log (P x)) z w

def LeviHolPerturb.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (ξ : (J → ℂ) → ℝ) (a φ : (J → ℂ) → ℂ) (z w : J → ℂ),
    ContDiffAt ℝ 2 ξ z → AnalyticAt ℂ a z → AnalyticAt ℂ φ z → φ z = 0 → fderiv ℂ φ z w = 0 →
    ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z ∧
      ξ z * (‖a z + φ z‖ ^ 2 - ‖a z‖ ^ 2) = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0 ∧
      fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z (Complex.I • w) = 0 ∧
      leviForm (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z w = 0

def LeviCompHol.Statement : Prop :=
  ∀ (E F : Type) [Fintype E] [Fintype F] (g : (E → ℂ) → (F → ℂ)) (φ : (F → ℂ) → ℝ) (x w : E → ℂ),
    AnalyticAt ℂ g x → ContDiffAt ℝ 2 φ (g x) →
    leviForm (fun y => φ (g y)) x w = leviForm φ (g x) (fderiv ℂ g x w)

def LeviFSInvariant.Statement : Prop :=
  ∀ (M : Type) [Fintype M] (a b : M → ℂ) (c μ : ℂ), a ≠ 0 → c ≠ 0 →
    leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) (c • a) (c • b + μ • a) =
      leviForm (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) a b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

