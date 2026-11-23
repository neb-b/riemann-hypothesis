module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisDiscRingHomExtOfAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.AcrisDiscExt

theorem isUnit_natCast_of {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hu : IsUnit (l : R)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have h : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm
  have h' := h.map f
  rw [map_natCast] at h'
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hu.pow v).mul h'

theorem norm_l_disc_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖((l : ℕ) : Disc l u ρ)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : Disc l u ρ) = ofPre l u ρ (algebraMap A (PreDisc l u ρ) ((l : A) ^ 1 * u ^ 0) *
      IsLocalization.Away.invSelf (l : A) ^ 0) := by
    simp
  rw [e, norm_ofPre]
  refine gauge_le l u ρ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, ?_, rfl⟩)
  rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']

theorem norm_pow_mul_le (l : ℕ) [Fact l.Prime] {K : FinExt l} (bk : BK K) (w : bk.DA bk.ρ₀) (r : ℕ) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r * w‖ ≤ (l : ℝ)⁻¹ ^ r * ‖w‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_l_disc_le l _ _) ih (norm_nonneg _) (by positivity))

theorem acris_disc_ext : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  intro l hl K bk γ γ' h hγ hγ'

  have h0 : ∀ s : Per.Acris0 l,
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) = γ' (algebraMap (Per.Acris0 l) (Per.Acris l) s) := by
    intro s
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
    have e : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a :=
      Subtype.ext (by simpa using hn)
    have e' := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e
    rw [map_mul, map_pow, map_natCast, ← GlobalTheory.RingIface.tower l] at e'
    have e1 := congrArg γ e'
    have e2 := congrArg γ' e'
    rw [map_mul, map_pow, map_natCast] at e1 e2
    refine ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n).mul_right_cancel ?_
    exact e1.trans ((h a).trans e2.symm)
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  ext x
  have hb : ∀ r : ℕ, ‖γ x - γ' x‖ ≤ 2 * (l : ℝ)⁻¹ ^ r := by
    intro r
    obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    have hs := h0 s
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hs, add_sub_add_left_eq_sub,
      ← mul_sub]
    have hw : ‖γ z - γ' z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hγ z, hγ' z])
    refine (norm_pow_mul_le l bk (γ z - γ' z) r).trans ?_
    exact mul_comm ((l : ℝ)⁻¹ ^ r) _ ▸ mul_le_mul_of_nonneg_left hw (by positivity)
  have ht : Filter.Tendsto (fun r : ℕ => 2 * (l : ℝ)⁻¹ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hl1).const_mul 2
  have hz : ‖γ x - γ' x‖ ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)

end GlobalTheory.AcrisDiscExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadius
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem vr_iterate_phi (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, (φc l)^[k] x ≠ 0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hl0 : (0 : ℝ) < l := by linarith
  intro k
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨hne, hv⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨((_root_.GlobalTheory.PMon.Gauss.vr_laws l 1 one_pos le_rfl).2.1 _ hne).1, ?_⟩
    intro r hr0 hr1
    rw [((_root_.GlobalTheory.PMon.Gauss.vr_laws l r hr0 hr1).2.1 _ hne).2]
    have h1 : 0 < r / l := div_pos hr0 hl0
    have h2 : r / l ≤ 1 := by rw [div_le_one hl0]; linarith
    rw [hv (r / l) h1 h2, pow_succ]
    have e : r / (l : ℝ) / (l : ℝ) ^ k = r / ((l : ℝ) ^ k * l) := by rw [div_div, mul_comm]
    rw [e]
    ring

theorem vr_sub_eq_int_mul : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  intro l _ h s hsh w w' hfix hw hw' hrat
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨cA, kA, sA⟩ := _root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l w hw
  obtain ⟨cB, kB, sB⟩ := _root_.GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope l w' hw'
  have key := _root_.GlobalTheory.PHomCalc.p_homogeneous_difference_linear l h s 1 hl2 hsh le_rfl (fun r => vr l r w) (fun r => vr l r w')
    cA cB kA kB sA sB ?_ ?_
  · obtain ⟨n, hn⟩ := key
    exact ⟨n, fun r hr => by simpa using hn r hr⟩
  · rintro r ⟨hr0, hr1⟩
    have e1 := (vr_iterate_phi l w' hw' h).2 r hr0 hr1
    rw [hfix, (_root_.GlobalTheory.PMon.Gauss.vr_laws l r hr0 hr1).2.2.1 w' s hw'] at e1
    show (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r
    linarith
  · rintro r ⟨hr0, hr1⟩
    have hlr0 : 0 < (l : ℝ) * r := mul_pos hl0 hr0
    have hlr1 : (l : ℝ) * r ≤ 1 := by rw [le_div_iff₀ hl0] at hr1; linarith
    obtain ⟨hmul, hphi, -, -⟩ := _root_.GlobalTheory.PMon.Gauss.vr_laws l (l * r) hlr0 hlr1
    have e := congrArg (vr l (l * r)) hrat
    rw [hmul _ _ (hphi w hw).1 hw', hmul _ _ hw (hphi w' hw').1, (hphi w hw).2,
      (hphi w' hw').2] at e
    have hc : (l : ℝ) * r / l = r := by field_simp
    rw [hc] at e
    show vr l (l * r) w - ((1 : ℕ) : ℝ) * vr l (l * r) w' = l * (vr l r w - ((1 : ℕ) : ℝ) * vr l r w')
    simp only [Nat.cast_one, one_mul]
    linarith

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActsTriviallyResidualOfComplexConjugate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.ResTrivConj

theorem map_eq_one_of_dual {R S n : Type} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n] (f : R →+* S)
    (A T' : GL n R) (T : Matrix n n R) (e : R) (t : ℕ) (hT : T.map f = 1) (he : f e = 1)
    (h : e • (T' : Matrix n n R)⁻¹.transpose =
      (A : Matrix n n R) * (e ^ t • T) * ((A⁻¹ : GL n R) : Matrix n n R)) :
    (T' : Matrix n n R).map f = 1 := by
  have hs : ∀ (c : R) (M : Matrix n n R), (c • M).map f = f c • M.map f := fun c M => by
    ext a b; simp
  have h1 := congrArg (fun M : Matrix n n R => M.map f) h
  simp only [Matrix.map_mul, hs, map_pow, he, hT, one_pow, one_smul, Matrix.mul_one] at h1
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f), Matrix.transpose_map,
    Matrix.transpose_eq_one, ← Matrix.coe_units_inv] at h1
  have h2 : ((T'⁻¹ : GL n R) : Matrix n n R).map f * (T' : Matrix n n R).map f = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]
  rwa [h1, Matrix.one_mul] at h2

theorem resTriv_conj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g g' : GE N, IsCj X g g' → ResTriv i s g → ResTriv i s g' := by
  intro D N X i s hsd g g' h hg
  have he : eps0 X i g' = eps0 X i g := by
    haveI := X.lPrime i
    have e : MulSemiringAction.toRingAut (GE N) N.Om g' =
        (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
      ext x; exact h x
    have : cycZ D.host.E N.Om (X.l i) g' = cycZ D.host.E N.Om (X.l i) g := by
      simp only [cycZ, MonoidHom.comp_apply]
      rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    simp only [eps0, MonoidHom.comp_apply, this]
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, by rw [he]; exact h2⟩
  obtain ⟨A, hA⟩ := hsd
  have hA' := hA g g' h
  rw [Tdual, he, ← Tgl_coe i s g'] at hA'
  rw [← Tgl_coe i s g']
  exact map_eq_one_of_dual _ A _ _ _ _ h1 h2 hA'

end GlobalTheory.ResTrivConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsComp
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.coeff_mem_of_mem_map {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (i : ι) (J : Ideal S) {y : A} (hy : y ∈ J.map s) : TB.c i y ∈ J := by
  have key : ∀ a, TB.c i (a * y) ∈ J := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      intro a
      rw [mul_comm, TB.c_mul]
      exact J.mul_mem_right _ hw
    | zero => intro a; rw [mul_zero, map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add (f := _)]; exact J.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

def TopBasis.comp {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) {A' : Type} [CommRing A'] {t : A →+* A'} {κ : Type}
    (TB' : TopBasis t (I.map s) κ) : TopBasis (t.comp s) I (ι × κ) where
  b p := t (TB.b p.1) * TB'.b p.2
  c p := (TB.c p.1).comp (TB'.c p.2)
  c_mul p a x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp]
    rw [TB'.c_mul, TB.c_mul]
  c_self p := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul, TB'.c_self, mul_one, TB.c_self]
  c_ne p q h := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul]
    by_cases hj : p.2 = q.2
    · rw [hj, TB'.c_self, mul_one, TB.c_ne]
      intro hi; exact h (Prod.ext hi hj)
    · rw [TB'.c_ne _ _ hj, mul_zero, map_zero]
  fin x n := by
    have hS := TB'.fin x n
    refine ((Set.Finite.biUnion hS fun j _ => TB.fin (TB'.c j x) n).prod hS).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, AddMonoidHom.coe_comp, Function.comp_apply] at hp
    have h2 : TB'.c p.2 x ∉ (I.map s) ^ n := fun h =>
      hp (TB.coeff_mem_of_mem_map p.1 _ (by rwa [← Ideal.map_pow] at h))
    exact ⟨Set.mem_biUnion (x := p.2) h2 hp, h2⟩
  approx x n F hF := by
    classical
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp] at hF ⊢
    have hS := TB'.fin x n
    set G : Finset κ := F.image Prod.snd ∪ hS.toFinset with hG
    set Fi : Finset ι := F.image Prod.fst with hFi
    have h1 : x - ∑ j ∈ G, t (TB'.c j x) * TB'.b j ∈ (I ^ n).map (t.comp s) := by
      have := TB'.approx x n G (fun j hj => by
        by_contra h
        exact hj (Finset.mem_union_right _ (hS.mem_toFinset.2 h)))
      rwa [← Ideal.map_pow, Ideal.map_map] at this
    have h2 : ∀ j, t (TB'.c j x) * TB'.b j - ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F),
        t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) ∈ (I ^ n).map (t.comp s) := by
      intro j
      have := TB.approx (TB'.c j x) n (Fi.filter (fun i => (i, j) ∈ F)) (fun i hi => by
        apply hF (i, j)
        intro hij
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hij, hij⟩))
      have h' := Ideal.mem_map_of_mem t this
      rw [Ideal.map_map] at h'
      have h'' := Ideal.mul_mem_right (TB'.b j) _ h'
      convert h'' using 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    have hsub : F ⊆ Fi ×ˢ G := fun p hp =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
    have h3 : ∑ p ∈ F, t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) =
        ∑ j ∈ G, ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F), t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) := by
      simp_rw [Finset.sum_filter]
      rw [← Finset.sum_product_right (s := Fi) (t := G)
        (f := fun p => if p ∈ F then t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) else 0)]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    rw [h3]
    have := Ideal.add_mem _ h1 (Ideal.sum_mem (t := G) _ fun j _ => h2 j)
    convert this using 1
    rw [Finset.sum_sub_distrib]; ring
  complete := by rw [← Ideal.map_map]; exact TB'.complete
  i₀ := (TB.i₀, TB'.i₀)
  b_i₀ := by simp [TB.b_i₀, TB'.b_i₀]

theorem topBasis_comp_exists : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type)
    (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ),
      (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  intro S A _ _ s I ι TB A' _ t I' κ TB' hI
  subst hI
  exact ⟨TB.comp TB', fun _ _ => rfl, fun _ _ _ => rfl⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.AinfDiv
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem cc_l : WittVector.constantCoeff (p := l) (R := OCb l) ((l : ℕ) : Ainf l) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

theorem dvd_iff (y : Ainf l) :
    ((l : ℕ) : Ainf l) ∣ y ↔ WittVector.constantCoeff (p := l) (R := OCb l) y = 0 := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem dvd_E : ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  have h := bk.monic.as_sum
  have : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
    change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
    conv_lhs => rw [h]
    rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_add (f := _), map_pow, add_sub_cancel_left, map_sum]
  refine Finset.dvd_sum fun i hi => ?_
  obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hd, map_mul, map_mul, map_mul, map_natCast, map_natCast, mul_assoc]
  exact dvd_mul_right _ _

theorem cc_E : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) = bk.flat ^ bk.Ep.natDegree := by
  have h := (dvd_iff _).1 (dvd_E bk)
  rw [map_sub, sub_eq_zero, map_pow, bk.ev_X] at h
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h ⊢
  exact h

theorem cc_E_ne : WittVector.constantCoeff (p := l) (R := OCb l) (bk.ev bk.E) ≠ 0 := by
  intro h
  have hu := (isUnit_inclW_of_span bk.span_ev).map (WittVector.constantCoeff (p := l) (R := Cb l))
  rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, ← WittVector.constantCoeff_apply, h,
    map_zero] at hu
  exact not_isUnit_zero hu

theorem flat_ne : bk.flat ≠ 0 := by
  intro h
  apply cc_E_ne bk
  rw [cc_E, h, zero_pow bk.deg_pos.ne']

theorem flat_not_unit : ¬ IsUnit bk.flat := by
  intro h
  have h1 : IsUnit (bk.ev bk.E) := by
    refine GlobalTheory.Per.AinfComplete.witt_isUnit _ ?_
    rw [cc_E]; exact h.pow _
  have h2 : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have := h1.map (Per.θ l)
  rw [h2] at this
  exact not_isUnit_zero this

theorem flat_nil : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 bk.flat) :=
  GlobalTheory.Per.AinfComplete.nilpotent_of_not_isUnit l _ fun h =>
    flat_not_unit bk (GlobalTheory.Per.AinfComplete.perfection_isUnit _ h)

theorem flat_haus (x : OCb l) (hx : ∀ n, bk.flat ^ n ∣ x) : x = 0 :=
  GlobalTheory.Per.AinfComplete.perfection_haus (flat_nil bk) x hx

theorem complete : IsAdicComplete (Ideal.span {bk.flat}) (OCb l) := {
  haus' x hx := by
    refine flat_haus bk x fun n => ?_
    have := hx n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero] at this
    exact Ideal.mem_span_singleton.1 this,
  prec' := (GlobalTheory.Per.AinfComplete.precomplete_of_summ
    (GlobalTheory.Per.AinfComplete.summ_of_tails
      (GlobalTheory.Per.AinfComplete.perfection_tails (flat_nil bk)))).prec' }

theorem dvd_of_dvd_X_mul (y : Ainf l) (h : ((l : ℕ) : Ainf l) ∣ bk.ev X * y) : ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff] at h ⊢
  rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (flat_ne bk)

theorem dvd_of_forall (y : Ainf l) (h : ∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) :
    ((l : ℕ) : Ainf l) ∣ y := by
  rw [dvd_iff]
  refine flat_haus bk _ fun m => ?_
  obtain ⟨z, hz⟩ := h m
  rw [dvd_iff, map_sub, sub_eq_zero, map_mul, map_pow, bk.ev_X] at hz
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at hz ⊢
  rw [hz]
  exact dvd_mul_right _ _


include bk in
theorem mem_pow (n : ℕ) (y : Ainf l)
    (h : ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2)) :
    y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n := by
  rw [← bk.span_ev] at h ⊢
  have h1 : (Ideal.span {((l : ℕ) : Ainf l)} ⊔ Ideal.span {bk.ev bk.E}) ^ (2 * n + 2) ≤
      Ideal.span {((l : ℕ) : Ainf l)} ^ (n + 1) ⊔ Ideal.span {bk.ev bk.E} ^ (n + 1) := by
    rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring]
    exact Ideal.sup_pow_add_le_pow_sup_pow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (h1 h)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  have hb : ((l : ℕ) : Ainf l) ∣ b := by
    rw [dvd_iff]
    have := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) huv
    simp only [map_add (f := _), map_mul, map_pow, cc_l, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul,
      zero_add] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (cc_E_ne bk))
  obtain ⟨b', rfl⟩ := hb
  have hy : y = a * ((l : ℕ) : Ainf l) ^ n + b' * bk.ev bk.E ^ (n + 1) := by
    rw [← sub_eq_zero]
    apply ainf_torsionFree
    linear_combination -huv
  rw [hy]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_right_mono le_sup_left n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · refine Ideal.pow_right_mono le_sup_right n ?_
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 ⟨b' * bk.ev bk.E, by ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈
        (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) →
      y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧
    (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧
    (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧
    bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧
    ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree :=
  fun _ _ _ bk => ⟨mem_pow bk, dvd_of_dvd_X_mul bk, dvd_of_forall bk, flat_ne bk, flat_not_unit bk,
    complete bk, dvd_E bk⟩

end GlobalTheory.BSP.AinfDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheorem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedRegular

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem regular_onto (h : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) :
    (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
    (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
    ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  refine ⟨fun K b hb hg => ?_, fun u => ?_, fun K w => ?_⟩
  · have hu : IsUnit (T.eB b) := by
      refine h.regular C K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hgK => ?_
      obtain ⟨x, hx⟩ := hg g hgK
      refine ⟨x, ?_⟩
      rw [← T.actB, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
      rfl
    simpa using hu.map T.eB.symm
  · obtain ⟨x, hx⟩ := GlobalTheory.Published.FontaineBcris.oneSubPhiOnto_of_filZero (h.ontoFilZero C) (T.eB u)
    refine ⟨T.eB.symm x, T.eB.injective ?_⟩
    rw [map_sub, T.frob, RingEquiv.apply_symm_apply, hx]
  · obtain ⟨x, hx, hF⟩ := h.fundOnto C (T.eD w)
    refine ⟨T.eB.symm x, T.eB.injective ?_, ?_⟩
    · rw [T.frob, RingEquiv.apply_symm_apply, hx]
    · rw [T.fil, map_sub, hC.ι, RingEquiv.apply_symm_apply]
      exact hF

end GlobalTheory.MemLoc.TiedRegular
end

