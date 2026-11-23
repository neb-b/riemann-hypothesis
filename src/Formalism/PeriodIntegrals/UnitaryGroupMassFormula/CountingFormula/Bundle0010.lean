module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.DdSNeZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichESymmApply
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_int (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {x v : (VS D).V} (hx : x ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT x v := by
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' x hx)
  exact ⟨o, ho⟩

theorem smul_int_mem (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : D.host.E}
    (hk : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = k) {v : (VS D).V} (hv : v ∈ Λ) : k • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  rw [algebraMap_smul]
  exact Λ.smul_mem o hv

theorem eich_conds (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (D.sp.hypE a) = 0 ∧ (VS D).hT (D.sp.hypE a) ((2 : D.host.E) • y0) = 0 ∧
    (VS D).hT ((2 : D.host.E) • y0) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) + (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 ∧
    (-2 * (VS D).hT y0 y0) + star (-2 * (VS D).hT y0 y0) +
      (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 := by
  have hh : star ((VS D).hT y0 y0) = (VS D).hT y0 y0 := (VS D).herm.eq y0 y0
  have h22 : (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 4 * (VS D).hT y0 y0 := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, map_ofNat, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨D.sp.hyp_ee a a, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, hy.1 a, smul_zero]
  · rw [LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a, map_zero, smul_zero]
  · rw [h22]
    ring
  · have hs2 : star (-2 : D.host.E) = -2 := by simp
    rw [h22, star_mul', hs2, hh]
    ring

theorem eich_conds_neg (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (-((2 : D.host.E) • y0)) = 0 ∧
    (VS D).hT (-((2 : D.host.E) • y0)) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) +
      (VS D).hT (-((2 : D.host.E) • y0)) (-((2 : D.host.E) • y0)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_smul, hy.1 a, smul_zero, neg_zero]
  · rw [map_neg, LinearMap.neg_apply, LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a,
      map_zero, smul_zero, neg_zero]
  · rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, LinearMap.map_smulₛₗ₂, map_smul, map_ofNat,
      smul_eq_mul, smul_eq_mul]
    ring

def eichE (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0))
    (eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0))
    (LinearMap.ext fun v => by
      obtain ⟨he, -, -, -, -⟩ := eich_conds D a hy
      obtain ⟨n2, n3, n4⟩ := eich_conds_neg D a hy
      have := eich_inv D he n2 n3 n4 v
      rw [neg_neg] at this
      exact this)
    (LinearMap.ext fun v => by
      obtain ⟨he, h2, h3, h4, -⟩ := eich_conds D a hy
      exact eich_inv D he h2 h3 h4 v)

theorem eichE_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    eichE D a y0 hy v = eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichE_symm_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    (eichE D a y0 hy).symm v = eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichL_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {e y : (VS D).V} {c : D.host.E} (he : e ∈ Λ) (hy : y ∈ Λ)
    (hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c) {v : (VS D).V} (hv : v ∈ Λ) :
    eichL D e y c v ∈ Λ := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  exact Λ.add_mem (Λ.sub_mem (Λ.add_mem hv (smul_int_mem D (unimod_int D hU he hv) hy))
    (smul_int_mem D (unimod_int D hU hy hv) he)) (smul_int_mem D hc (smul_int_mem D (unimod_int D hU he hv) he))

theorem eichE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {y0 : (VS D).V}
    (hy : InW D y0) (hyΛ : y0 ∈ Λ) : eichE D a y0 hy ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hF.2.1
  have hea : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hFe] at h1
  obtain ⟨he, h2, h3, -, h5⟩ := eich_conds D a hy
  have hy2 : (2 : D.host.E) • y0 ∈ Λ := smul_int_mem D (k := (2 : D.host.E)) ⟨2, map_ofNat _ 2⟩ hyΛ
  have hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = -2 * (VS D).hT y0 y0 := by
    obtain ⟨o, ho⟩ := unimod_int D hU hyΛ hyΛ
    exact ⟨-2 * o, by rw [map_mul, ho, map_neg, map_ofNat]⟩
  have hP : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE),
      (∀ b, (VS D).hT (D.sp.hypE b) x = 0) ∧ (VS D).hT y0 x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨fun b => D.sp.hyp_ee b c, by rw [← (VS D).herm.eq (D.sp.hypE c) y0, hy.1 c, map_zero]⟩
    | zero => simp
    | add x z _ _ hx hz => exact ⟨fun b => by rw [map_add (f := _), hx.1 b, hz.1 b, add_zero], by
        rw [map_add (f := _), hx.2, hz.2, add_zero]⟩
    | smul c x _ hx => exact ⟨fun b => by rw [map_smul, hx.1 b, smul_zero], by
        rw [map_smul, hx.2, smul_zero]⟩
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE), eichE D a y0 hy x = x := by
    intro x hx
    obtain ⟨h1, h2'⟩ := hP x hx
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, h1 a, h2', smul_zero, zero_smul, add_zero, sub_zero]
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  have hy0z : (VS D).hT y0 D.sp.zm = 0 := by
    rw [← (VS D).herm.eq D.sp.zm y0, hy.2.2, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    exact eich_isom D he h2 h3 h5 u v
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => eichL_lat D hU hea hy2 hc hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨(eichE D a y0 hy).symm v, ?_, (eichE D a y0 hy).apply_symm_apply v⟩
      rw [eichE_symm_apply]
      exact eichL_lat D hU hea (Λ.neg_mem hy2) hc hv
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
      rw [← hFe]
      exact Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have hex : (VS D).hT (D.sp.hypE a) x = 0 := by
      have h1 : x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range F0.e)) := hx
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker] at h1
      exact h1 _ (by rw [hFe]; exact Submodule.subset_span ⟨a, rfl⟩)
    show (eichE D a y0 hy) x - x ∈ Submodule.span D.host.E (Set.range F0.e)
    rw [eichE_apply, hFe]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, hex, zero_smul, add_zero, smul_zero, add_sub_cancel_left, zero_sub]
    rw [sub_sub_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [hFe]
    exact hspan _ (Submodule.subset_span ⟨b, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, hzm a, hy0z, smul_zero, zero_smul, add_zero, sub_zero]

theorem eichE_pW (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    pW D (eichE D a y0 hy v) = pW D v + (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0) := by
  rw [eichE_apply]
  have hf : ∀ b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hy2 : ∀ b, (VS D).hT (D.sp.hypF b) y0 = 0 := hy.2.1
  simp only [pW, eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_sub, map_smul, hf, hy.1, hy2, hy.2.2,
    D.sp.hyp_ee, (D.sp.hyp_orthz a).1, smul_eq_mul, mul_zero, add_zero, sub_zero, zero_add, mul_ite,
    mul_one, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, add_smul, sub_smul, zero_div]
  module

theorem eichE_hTe (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (a' : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE a') (eichE D a y0 hy v) = (VS D).hT (D.sp.hypE a') v := by
  rw [eichE_apply]
  simp [eichL, D.sp.hyp_ee, hy.1 a']

theorem eich_all (hN : UnipotentIntegralIsGroup) (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (y0 : Fin D.R.rS → (VS D).V)
    (hy : ∀ a, InW D (y0 a)) (hyΛ : ∀ a, y0 a ∈ Λ) :
    ∃ n ∈ N0 F0 Λ, ∀ v, pW D (n v) = pW D v + ∑ a, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) := by
  have key : ∀ s : Finset (Fin D.R.rS), ∃ n ∈ N0 F0 Λ, ∀ v,
      pW D (n v) = pW D v + ∑ a ∈ s, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) ∧
      ∀ a', (VS D).hT (D.sp.hypE a') (n v) = (VS D).hT (D.sp.hypE a') v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl _ _, (hN D F0 Λ).1, fun v => ⟨by simp, fun a' => rfl⟩⟩
    | @insert a s ha ih =>
      obtain ⟨n, hn, hv⟩ := ih
      refine ⟨n.trans (eichE D a (y0 a) (hy a)),
        (hN D F0 Λ).2.2 n hn _ (eichE_mem D F0 Λ hF a (hy a) (hyΛ a)), fun v => ⟨?_, fun a' => ?_⟩⟩
      · rw [LinearEquiv.trans_apply, eichE_pW, (hv v).1, (hv v).2 a, Finset.sum_insert ha]
        abel
      · rw [LinearEquiv.trans_apply, eichE_hTe, (hv v).2 a']
  obtain ⟨n, hn, hv⟩ := key Finset.univ
  exact ⟨n, hn, fun v => (hv v).1⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MemSmulLatCoord
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

def InP (ϖ : 𝒪[F]) (u : F) : Prop := ∃ o : 𝒪[F], u = (ϖ : F) * o

theorem e_alg (e : E ≃ₐ[F] F × F) (c : F) : e (algebraMap F E c) = (c, c) := by
  first
  | (rw [e.commutes]; rfl)
  | simp [e.commutes]

theorem pi_smulF (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπ : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) (c : F) (x : V) :
    π (algebraMap F E c • x) = (c • (π x).1, c • (π x).2) := by
  rw [hπ, e_alg]

theorem mem_smulLat_iff' (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (c : E) (x : V) :
    x ∈ H.smulLat c Λ ↔ ∃ y ∈ Λ, x = c • y := by
  unfold Loc.HermSp.smulLat
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩
    | smul a z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨a • y, Λ.smul_mem a hy, ?_⟩
      first
      | exact smul_comm a c y
      | exact (smul_comm c a y).symm
      | (show ((a : E)) • c • y = c • ((a : E) • y); exact smul_comm _ _ _)
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem mem_smulLat_coord (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) (ϖ : 𝒪[F]) (x : V) :
    x ∈ H.smulLat (algebraMap F E ϖ) Λ ↔ (∀ k, InP ϖ ((π x).1 k)) ∧ ∀ k, InP ϖ ((π x).2 k) := by
  rw [mem_smulLat_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pi_smulF e π hπa]
    obtain ⟨h1, h2⟩ := (hπL y).1 hy
    exact ⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩,
      fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩
  · rintro ⟨h1, h2⟩
    choose o1 ho1 using h1
    choose o2 ho2 using h2
    refine ⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩
    · rw [hπL, AddEquiv.apply_symm_apply]
      exact ⟨fun k => (o1 k).2, fun k => (o2 k).2⟩
    · apply π.injective
      rw [pi_smulF e π hπa, AddEquiv.apply_symm_apply]
      ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]

theorem inP_sub_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {u w : F}
    (hu : u ∈ 𝒪[F]) (hw : w ∈ 𝒪[F]) : InP ϖ (u - w) ↔ resF F u = resF F w := by
  have key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d := by
    intro d
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o, Subtype.ext (by simp [ho])⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, by simp⟩
  have e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩ := by
    first
    | simp [resF, hu]
    | (unfold resF; rw [dite_eq_left hu])
  have e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩ := by
    first
    | simp [resF, hw]
    | (unfold resF; rw [dite_eq_left hw])
  have hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F) := rfl
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ
  rw [e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem mk_eq_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) x =
        Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) y ↔
      (∀ k, resF F ((π x).1 k) = resF F ((π y).1 k)) ∧ ∀ k, resF F ((π x).2 k) = resF F ((π y).2 k) := by
  rw [Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]
  obtain ⟨hx1, hx2⟩ := (hπL x).1 hx
  obtain ⟨hy1, hy2⟩ := (hπL y).1 hy
  simp only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k))
    (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))

theorem mem_span_irr_iff (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (ϖ : 𝒪[F]) (z : E) :
    z ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ InP ϖ (e z).1 ∧ InP ϖ (e z).2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (hO a).1 a.2
    refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>
      simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]
  · rintro ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩
    have hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O := by
      rw [hO, AlgEquiv.apply_symm_apply]
      exact ⟨o1.2, o2.2⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply e.injective
    ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]

theorem resF_bil {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) :
    resF F (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ∑ k, ∑ l, resF F (x k) * IsLocalRing.residue 𝒪[F] (Ph k l) * resF F (y l) := by
  have hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩ := by
    intro a ha
    first
    | simp [resF, ha]
    | (unfold resF; rw [dite_eq_left ha])
  have hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F) := by
    first
    | (push_cast; rfl)
    | (simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]; rfl)
    | (simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul])
    | (push_cast; simp)
    | simp
  have hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩ := fun k => hc _ (hx k)
  have hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩ := fun l => hc _ (hy l)
  have hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z := fun z => hc z z.2
  rw [hsum, hc']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hxk, hyl]

theorem bil_mem {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : (∑ k, ∑ l, x k * (Ph k l : F) * y l) ∈ 𝒪[F] := by
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepGood
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_mem_ddS_zpow (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := PI.TripleFrameDeterminant.W.ddS_ne_zero D
  have hle : ddS D ^ k ≤ 1 := by
    rw [ddS, ← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  have h := FractionalIdeal.inv_anti_mono (pow_ne_zero k h0) hle
  rw [inv_one] at h
  rw [zpow_neg, zpow_natCast]
  exact h (FractionalIdeal.one_mem_one _)

theorem flag_gram (D : Formalism.BasicNotions.D7) {T' : D.host.E} (G : FlagG (VS D) D.R.rS T') (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (G.fvec a) (G.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0 := by
  have hs : ∀ x y, (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
    fun x y => ((VS D).herm.eq x y).symm
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_norm]
    | cast j =>
      rw [hs]
      simp [FlagG.fvec, G.z_orth j]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, G.z_orth i]
    | cast j => simp [FlagG.fvec, G.e_iso i j]

theorem good_places_integral : GoodEZ := by
  intro D T T' F0 Λ Z F' hF'
  obtain ⟨hT, -, -, hFr, hZ⟩ := hF'
  have hfr : fr D (F'.fl.e, F'.fl.z) = F'.fl.fvec := rfl
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hfr]
    have h := PI.CntNotIntW.frame_mem Λ F' hFr.2 hT.1.1 b 1 (one_mem_ddS_zpow D _)
    rwa [one_smul] at h
  · rw [hfr, ← hZ]
    rfl
  · rw [hfr]
    exact flag_gram D F'.fl a b

end PI.UnitaryGroupMassFormula.CntFormula
end
end

