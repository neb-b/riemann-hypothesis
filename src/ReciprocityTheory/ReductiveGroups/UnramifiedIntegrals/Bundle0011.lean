module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Formalism.TorsionNormIteration.LubinTateExample
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Abstract

variable {K : Type} [NormedField K]

structure LawD (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) : Prop where
  lam0 : constantCoeff lam = 0
  lam1 : coeff 1 lam = 1
  Φ0 : MvPowerSeries.constantCoeff Φ = 0
  Φint : IntegralMv Φ
  log : lam.subst Φ = atX lam + atY lam

structure HD (σ : K →+* K) (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K)
    (a : K) : Prop extends LawD lam Φ where
  A0 : constantCoeff A = 0
  Aint : IntegralPS A
  Alog : lam.subst A = C a * lam
  a_ne : ‖σ a - a‖ = 1
  a_sq : σ (σ a) = a

structure QCls (l : ℕ) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K) (b : K)
    (D : PowerSeries K) : Prop where
  D0 : constantCoeff D = 0
  dInt : IntegralPS (PowerSeries.derivative D)
  add : DivByMv (l : K) (D.subst Φ - atX D - atY D)
  eig : DivBy (l : K) (D.subst A - C b * D)

structure HomCls (l : ℕ) (Φ₁ : MvPowerSeries (Fin 2) K) (A₁ : PowerSeries K)
    (Φ₂ : MvPowerSeries (Fin 2) K) (A₂ : PowerSeries K) (g : PowerSeries K) : Prop where
  g0 : constantCoeff g = 0
  gInt : IntegralPS g
  add : DivByMv (l : K) (g.subst Φ₁ - Φ₂.subst ![atX g, atY g])
  eig : DivBy (l : K) (g.subst A₁ - A₂.subst g)

def desc (l : ℕ) (D : PowerSeries K) : PowerSeries K := PowerSeries.mk fun m => coeff (l * m) D

def d2 (Φ : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) Φ

end Abstract


open Classical in
def lgS {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  if h : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X then h.choose else 0

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KmuInclDenseRange
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion (Subfield.le_topologicalClosure (Kmu l))

theorem kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl

theorem kmuIncl_isometry : Isometry (kmuIncl l) :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)

theorem kmuIncl_denseRange : DenseRange (kmuIncl l) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩

theorem kurFrob : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  have hiso : Isometry ((kmuIncl l).comp s) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1])
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hdi : IsDenseInducing (kmuIncl l) :=
    (kmuIncl_isometry l).isUniformInducing.isDenseInducing (kmuIncl_denseRange l)
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    hdi.extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  · rw [hl, norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  · intro x
    refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
      (isClosed_eq hσc.norm continuous_norm) (fun y => ?_)
    rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  · intro x hx
    have hopen : IsOpen (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
      (kmuIncl_denseRange l).open_subset_closure_inter hopen (by simpa using hx)
    have hcl : IsClosed {x : MaximalUnramifiedExtension l | ‖σ x - x ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖} :=
      isClosed_le (hσc.sub (continuous_pow l)).norm continuous_const
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hy1, y, rfl⟩
    have hy : ‖y‖ ≤ 1 := by
      rw [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
      exact hy1
    have := hs2 y hy
    show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
    rw [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
    exact this
  · intro x hx
    exact kur_discrete l x.2 hx

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSer
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem zetaRoot_mem_cyclotomicSubring_self (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem zetaRoot_ne_zero (e : ℕ) : zetaC e ≠ 0 := by
  exact Complex.exp_ne_zero _

private theorem dvd_and_eq_div_of_mem_Tm {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    t.1 ∣ m ∧ 0 < t.1 ∧ t.2.2 = m / t.1 ∧ t.1 * t.2.2 = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd hm, rfl, Nat.mul_div_cancel' hdvd⟩

private theorem zetaC_div_eq_pow_of_dvd {m a : ℕ} (hm : 0 < m) (ha : a ∣ m) : zetaC (m / a) = zetaC m ^ a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at ha
    omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  unfold zetaC
  rw [← Complex.exp_nat_mul, Nat.cast_div ha ha']
  congr 1
  field_simp

theorem zetaRoot_pow_mem_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    zetaC t.2.2 ^ t.2.1 ∈ Rm m ∧ (zetaC t.2.2 ^ t.2.1)⁻¹ ∈ Rm m := by
  obtain ⟨hdvd, _, he, _⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have hz : zetaC t.2.2 ^ t.2.1 = zetaC m ^ (t.1 * t.2.1) := by
    rw [he, zetaC_div_eq_pow_of_dvd hm hdvd, pow_mul]
  have hzm : zetaC m ^ m = 1 := by
    unfold zetaC
    rw [← Complex.exp_nat_mul]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_two_pi_mul_I
  have hinv : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hm, hzm]
  rw [hz]
  constructor
  · exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _
  · rw [← inv_pow, hinv, ← pow_mul]
    exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _

theorem norm_zetaRoot_pow_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    ‖zetaC t.2.2 ^ t.2.1‖ = 1 := by
  rw [norm_pow, zetaC, Complex.norm_exp]
  simp

theorem convergesOnDisk_eisensteinFourCubeSeries : Conv aC := by
  rw [aC_eq]
  exact isMF_AA.conv

theorem convergesOnDisk_discriminantSeries : Conv dC := by
  rw [dC_eq]
  exact isMF_DD.conv

theorem evalSeries_eisensteinFourCubeSeries (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  rw [aC_eq]
  exact isMF_AA.ev_eq τ

theorem evalSeries_discriminantSeries (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  rw [dC_eq]
  exact isMF_DD.ev_eq τ

theorem eisensteinFourCubeSeries_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  rw [aC, PowerSeries.coeff_map, aZ, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, e4Z]
  simp

theorem discriminantSeries_coeff_zero : PowerSeries.coeff 0 dC = 0 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_zero]
  simp

theorem discriminantSeries_coeff_one : PowerSeries.coeff 1 dC = 1 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_one]
  simp

theorem facSer_coeffIn {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    CoeffIn (Rm m) (facSer m t) := by
  obtain ⟨hc, _⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hA : CoeffIn (Rm m) aC := CoeffIn.map_int _ _
  have hD : CoeffIn (Rm m) dC := CoeffIn.map_int _ _
  unfold facSer
  exact ((hA.xp m).mul (hD.sub1 hc _)).sub ((hA.sub1 hc _).mul (hD.xp m))

theorem facSer_conv {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : Conv (facSer m t) := by
  have hc : ‖zetaC t.2.2 ^ t.2.1‖ ≤ 1 := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ (dvd_and_eq_div_of_mem_Tm hm ht).2.1.ne'
  unfold facSer
  exact ((convergesOnDisk_eisensteinFourCubeSeries.xp hm.ne').mul (convergesOnDisk_discriminantSeries.sub1 hc hk)).sub
    ((convergesOnDisk_eisensteinFourCubeSeries.sub1 hc hk).mul (convergesOnDisk_discriminantSeries.xp hm.ne'))

theorem facSer_ev {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have he0 : 0 < t.2.2 := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hm hdvd) ha0
  have hq := qm_norm_lt_one hm τ
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hA := convergesOnDisk_eisensteinFourCubeSeries
  have hD := convergesOnDisk_discriminantSeries
  have hpt : zetaC t.2.2 ^ t.2.1 * qm m τ ^ (t.1 ^ 2) = qm 1 (pt t.1 t.2.1 t.2.2 τ) := by
    rw [qm_pt ha0 he0, hae]
  unfold facSer fac
  rw [ev_sub ((hA.xp hm.ne').mul (hD.sub1 hc hk)) ((hA.sub1 hc hk).mul (hD.xp hm.ne')) hq,
    ev_mul (hA.xp hm.ne') (hD.sub1 hc hk) hq, ev_mul (hA.sub1 hc hk) (hD.xp hm.ne') hq,
    ev_xp _ hm.ne', ev_xp _ hm.ne', evalSeries_rescaleExpand _ _ hk, evalSeries_rescaleExpand _ _ hk, qm_pow hm, hpt]
  simp only [evalSeries_eisensteinFourCubeSeries, evalSeries_discriminantSeries]

theorem LowUnit.facSub_left {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n < n') : LowUnit R (f - g) n u := by
  obtain ⟨hu, hui, hu0, hlow, hval⟩ := hf
  obtain ⟨_, _, _, hglow, _⟩ := hg
  refine ⟨hu, hui, hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hlow k hk, hglow k (hk.trans h), sub_zero]
  · rw [map_sub, hval, hglow n h, sub_zero]

theorem LowUnit.facSub_right {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n' < n) : LowUnit R (f - g) n' (-u') := by
  obtain ⟨_, _, _, hflow, _⟩ := hf
  obtain ⟨hu, hui, hu0, hglow, hval⟩ := hg
  refine ⟨neg_mem hu, by rw [inv_neg]; exact neg_mem hui, neg_ne_zero.2 hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hflow k (hk.trans h), hglow k hk, sub_zero]
  · rw [map_sub, hflow n' h, hval, zero_sub]

theorem hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (R : Subring ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) :
    LowUnit R (sub1 c k aC) 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  rw [sub1, coeff_xp, if_pos (dvd_zero k), Nat.zero_div, PowerSeries.coeff_rescale, pow_zero, one_mul,
    eisensteinFourCubeSeries_coeff_zero]

theorem hasUnitLeadingCoeff_rescaleExpand_discriminantSeries {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by
  refine ⟨hc, hc', hc0, fun n hn => ?_, ?_⟩
  · rw [sub1, coeff_xp]
    split_ifs with hd
    · have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
      subst h0
      rw [Nat.zero_div, PowerSeries.coeff_rescale, discriminantSeries_coeff_zero, mul_zero]
    · rfl
  · rw [sub1, coeff_xp, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hk), PowerSeries.coeff_rescale,
      pow_one, discriminantSeries_coeff_one, mul_one]

theorem rescaleExpand_one (k : ℕ) (f : PowerSeries ℂ) : sub1 1 k f = xp k f := by
  simp [sub1, PowerSeries.rescale_one]

theorem facSer_low {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (hne : t.1 ≠ t.2.2) :
    ∃ n0 u, LowUnit (Rm m) (facSer m t) n0 u := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  obtain ⟨hc, hci⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hc0 : zetaC t.2.2 ^ t.2.1 ≠ 0 := pow_ne_zero _ (zetaRoot_ne_zero _)
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hxa : LowUnit (Rm m) (xp m aC) 0 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries _ 1 hm.ne'
  have hxd : LowUnit (Rm m) (xp m dC) m 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_discriminantSeries (one_mem _) (by rw [inv_one]; exact one_mem _) one_ne_zero hm.ne'
  have h1 := hxa.mul (hasUnitLeadingCoeff_rescaleExpand_discriminantSeries hc hci hc0 hk)
  have h2 := (hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (Rm m) (zetaC t.2.2 ^ t.2.1) hk).mul hxd
  simp only [zero_add, one_mul] at h1 h2
  unfold facSer
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨_, _, h1.facSub_left h2 (by rw [← hae]; nlinarith)⟩
  · exact ⟨_, _, h1.facSub_right h2 (by rw [← hae]; nlinarith)⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.mdiff {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : MDiff f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.holo g

theorem IsMF.bdd {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : IsBoundedAtImInfty f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.bdd_at_infty g

theorem pt_im {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    (pt a b e τ).im = (a : ℝ) / e * τ.im := by
  have h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im := by
    rw [Complex.div_natCast_im]
    simp
    ring
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im := by
    rw [h1]
    have := τ.im_pos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  exact h1

theorem mdiff_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (fun τ => f (pt a b e τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rw [h2] at h3
    exact h3
  have hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} := by
    fun_prop
  refine (hf.comp hd hmap).congr fun z hz => ?_
  simp only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]

theorem tendsto_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) :
    Filter.Tendsto (pt a b e) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im := funext fun τ => pt_im ha he b τ
  rw [h]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : (0 : ℝ) < (a : ℝ) / e := by positivity
  exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap

theorem bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (fun τ => f (pt a b e τ)) := by
  exact hf.comp_tendsto (tendsto_pt ha he b)

theorem fac_mdiff {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : MDiff (fac t) := by
  have hA := isMF_AA.mdiff
  have hD := isMF_DD.mdiff
  exact (hA.mul (mdiff_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

theorem fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty (fac t) := by
  have hA := isMF_AA.bdd
  have hD := isMF_DD.bdd
  exact (hA.mul (bdd_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

theorem Gm_mdiff {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact (fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

theorem Gm_bdd {m : ℕ} (hm : 0 < m) : IsBoundedAtImInfty (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → IsBoundedAtImInfty (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact Filter.BoundedAtFilter.mul (fac_bdd (Tm_pos hm (hs (Finset.mem_insert_self t s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

theorem Gm_slash {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ τ
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp

theorem gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) (Gm m) := by
  refine ⟨{ toFun := Gm m
            slash_action_eq' := ?_
            holo' := Gm_mdiff hm
            bdd_at_cusps' := ?_ }, fun τ => rfl⟩
  · intro A hA
    obtain ⟨A, rfl⟩ := hA
    exact Gm_slash hm A
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [Gm_slash hm γ]
    exact Gm_bdd hm

end ReciprocityTheory.ChartRestriction.L1
end
end

