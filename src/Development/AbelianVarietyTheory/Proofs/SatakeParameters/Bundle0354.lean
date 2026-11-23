module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe v

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} (g : ∀ s, C.obj s →ₗ[R] E)

def famMap (p : ℕ) : Cube.Term C p →ₗ[R] (Finset ι → E) where
  toFun x s := g s (Cube.extend C p x s)
  map_add' x y := by funext s; simp
  map_smul' r x := by funext s; simp

theorem famMap_apply (p : ℕ) (x : Cube.Term C p) (s : Finset ι) :
    famMap g p x s = g s (Cube.extend C p x s) := rfl

theorem famMap_of_eq {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card = p) :
    famMap g p x s = g s (x ⟨s, h⟩) := by
  rw [famMap_apply, Cube.extend_apply_of_eq]

theorem famMap_of_ne {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card ≠ p) :
    famMap g p x s = 0 := by
  rw [famMap_apply, Cube.extend_apply_of_ne C x h, map_zero]

variable {g}

theorem famMap_d (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x)
    (m : ℕ) (x : Cube.Term C (m + 1)) :
    famMap g (m + 1 + 1) (Cube.d C (m + 1) x) = deltaL R ι E (famMap g (m + 1) x) := by
  funext t
  change _ = GlobalTheory.DI.delta (famMap g (m + 1) x) t
  unfold GlobalTheory.DI.delta
  by_cases ht : t.card = m + 1 + 1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [famMap_of_eq g _ ht, Cube.d_apply_extend, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : (t.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hi, ht]; omega
    rw [map_zsmul, famMap_apply, hres _ _ _ hn]
  · rw [famMap_of_ne g _ ht]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have h1 : 0 < t.card := Finset.card_pos.2 ⟨i, hi⟩
    rw [famMap_of_ne g _ (by rw [Finset.card_erase_of_mem hi]; omega), smul_zero]

theorem famMap_injective (hinj : ∀ s, s.Nonempty → Function.Injective (g s)) (m : ℕ) :
    Function.Injective (famMap g (m + 1)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext s
  have h := congrFun hx s.1
  rw [famMap_of_eq g x s.2] at h
  exact hinj s.1 (Finset.card_pos.1 (by rw [s.2]; omega)) (h.trans (map_zero _).symm)

variable {A : Finset ι → Submodule R E}

theorem cechC_apply_mem {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card = n + 1) : w s ∈ A s := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rwa [if_pos ⟨Finset.card_pos.1 (by omega), by omega⟩] at this

theorem cechC_apply_eq_zero {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card ≠ n + 1) : w s = 0 := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rw [if_neg (fun h' => h (by omega))] at this
  exact (Submodule.mem_bot R).1 this

theorem famMap_mem (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) (n : ℕ)
    (x : Cube.Term C (n + 1)) : famMap g (n + 1) x ∈ cechC A (n : ℤ) := by
  refine Submodule.mem_pi.2 fun s _ => ?_
  split_ifs with h
  · rw [famMap_of_eq g x (by omega : s.card = n + 1), ← hrange s h.1]
    exact LinearMap.mem_range_self _ _
  · rw [famMap_of_ne g x (fun h' => h ⟨Finset.card_pos.1 (by omega), by omega⟩)]
    exact Submodule.zero_mem _

theorem famMap_eq_of_agree {n : ℕ} (x : Cube.Term C (n + 1)) {w : Finset ι → E}
    (hw : w ∈ cechC A (n : ℤ)) (h : ∀ t : {s : Finset ι // s.card = n + 1}, w t.1 = g t.1 (x t)) :
    famMap g (n + 1) x = w := by
  funext s
  by_cases hs : s.card = n + 1
  · rw [famMap_of_eq g x hs]; exact (h ⟨s, hs⟩).symm
  · rw [famMap_of_ne g x hs, cechC_apply_eq_zero hw hs]

theorem famMap_surj (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) {n : ℕ}
    {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) : ∃ x, famMap g (n + 1) x = w := by
  have : ∀ s : {s : Finset ι // s.card = n + 1}, ∃ y, g s.1 y = w s.1 := fun s => by
    have h := cechC_apply_mem hw s.2
    rw [← hrange _ (Finset.card_pos.1 (by rw [s.2]; omega))] at h
    exact h
  choose x hx using this
  exact ⟨x, famMap_eq_of_agree x hw fun t => (hx t).symm⟩

end GlobalTheory.CechFam

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} {g : ∀ s, C.obj s →ₗ[R] E} {A : Finset ι → Submodule R E}

theorem famMap_mem_Z (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) : famMap g (n + 1) z.1 ∈ (GlobalTheory.PD.cech A).Z (n : ℤ) := by
  refine Submodule.mem_inf.2 ⟨famMap_mem hrange n z.1, ?_⟩
  rw [LinearMap.mem_ker]
  change deltaL R ι E (famMap g (n + 1) z.1) = 0
  rw [← famMap_d hres, LinearMap.mem_ker.1 z.2, map_zero]

def cocMap (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (Cube.d C (n + 1)) →ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
  Submodule.mkQ (((GlobalTheory.PD.cech A).B (n : ℤ)).submoduleOf ((GlobalTheory.PD.cech A).Z (n : ℤ))) ∘ₗ
    LinearMap.codRestrict ((GlobalTheory.PD.cech A).Z (n : ℤ)) (famMap g (n + 1) ∘ₗ (LinearMap.ker _).subtype)
      (famMap_mem_Z hrange hres n)

theorem cocMap_apply (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) :
    cocMap hrange hres n z = Submodule.Quotient.mk ⟨famMap g (n + 1) z.1, famMap_mem_Z hrange hres n z⟩ :=
  rfl

theorem cocMap_surjective (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    Function.Surjective (cocMap hrange hres n) := by
  intro c
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨x, hx⟩ := famMap_surj hrange (Submodule.mem_inf.1 hw).1
  have hd : Cube.d C (n + 1) x = 0 := by
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hw).2
  refine ⟨⟨x, LinearMap.mem_ker.2 hd⟩, ?_⟩
  rw [cocMap_apply]
  congr 1
  exact Subtype.ext hx

theorem ker_cocMap (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (cechClass C n) = LinearMap.ker (cocMap hrange hres n) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker, cocMap_apply, Submodule.Quotient.mk_eq_zero]
  change _ ↔ famMap g (n + 1) z.1 ∈ ((GlobalTheory.PD.cech A).C ((n : ℤ) - 1)).map (deltaL R ι E)
  rw [Submodule.mem_map]
  cases n with
  | zero =>
    rw [cechClass_zero_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, ZeroMemClass.coe_zero, map_zero]⟩
    · rintro ⟨y, hy, hyz⟩
      have hy0 : y = 0 := by
        funext s
        have := (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
        rw [if_neg (fun h => by
          have := Finset.card_pos.2 h.1
          push_cast at h
          omega)] at this
        exact (Submodule.mem_bot R).1 this
      rw [hy0, map_zero] at hyz
      exact Subtype.ext (famMap_injective hinj 0 (hyz.symm.trans (map_zero _).symm))
  | succ m =>
    rw [cechClass_succ_eq_zero_iff]
    have hc : (GlobalTheory.PD.cech A).C (((m + 1 : ℕ) : ℤ) - 1) = cechC A (m : ℤ) := by
      change cechC A _ = _
      congr 1
      push_cast
      ring
    rw [hc]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨famMap g (m + 1) y, famMap_mem hrange m y, ?_⟩
      rw [← famMap_d hres, hy]
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨x, rfl⟩ := famMap_surj hrange hy
      refine ⟨x, famMap_injective hinj (m + 1) ?_⟩
      rw [famMap_d hres]
      exact hyz

end GlobalTheory.CechFam


open GlobalTheory.CechFam in
theorem GlobalTheory.cechHomologyEquivFam : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  intro R _ ι _ E _ _ A C g hinj hrange hres n
  let e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
    ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm.trans
      ((Submodule.quotEquivOfEq _ _ (ker_cocMap hinj hrange hres n)).trans
        ((cocMap hrange hres n).quotKerEquivOfSurjective (cocMap_surjective hinj hrange hres n)))
  have he : ∀ z, e (cechClass C n z) = cocMap hrange hres n z := by
    intro z
    have h1 : ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm
        (cechClass C n z) = Submodule.Quotient.mk z := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [e, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨e, fun z w hw => ?_, fun z => ⟨⟨_, famMap_mem_Z hrange hres n z⟩, fun t => ?_⟩,
    fun x w hw => ?_⟩
  · rw [he, cocMap_apply]
    congr 1
    exact Subtype.ext (famMap_eq_of_agree z.1 (Submodule.mem_inf.1 w.2).1 hw)
  · exact famMap_of_eq g z.1 t.2
  · have hx := famMap_eq_of_agree x (Submodule.mem_inf.1 w.2).1 hw
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 w.2).2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqTopOfForallComplexPointsMemOpensStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_top_of_forall_complexPoints_mem_opens : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  first | (exact @GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (exact GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem) | (intros; apply GlobalTheory.MaxPt.eq_top_of_forall_cxPts_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximalStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  first | (exact @GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (exact GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (intros; apply GlobalTheory.MaxPt.exists_cxPts_ker_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenericForms
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

open TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.Generic

variable {N : ℕ}

def lin (c : Fin (N + 1) → ℂ) : MvPolynomial (Fin (N + 1)) ℂ := ∑ l, c l • MvPolynomial.X l

theorem lin_mem (c : Fin (N + 1) → ℂ) : lin c ∈ ProjSpace.grading ℂ N 1 := by
  unfold lin
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (ProjSpace.X_mem ℂ N l)

theorem exists_X_notMem (z : PSpace ℂ N) :
    ∃ l, (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℂ) ∉ z.asHomogeneousIdeal.toIdeal := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) ≤
      z.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact h l
  apply ProjectiveSpectrum.not_irrelevant_le z
  intro x hx
  exact hle (ProjSpace.irrelevant_le_span_X ℂ N hx)

theorem exists_finite_gen {Y : Scheme.{0}} [NoetherianSpace Y] (Z : Set Y) (hZ : IsClosed Z) :
    ∃ T : Set Y, T.Finite ∧ T ⊆ Z ∧ ∀ x ∈ Z, ∃ t ∈ T, t ⤳ x := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  haveI : Finite S := hSf.to_subtype
  refine ⟨Set.range fun s : S => (hSi s.1 s.2).genericPoint, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨⟨s, hs⟩, rfl⟩
    exact Set.mem_sUnion_of_mem ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).mem hs
  · rintro x ⟨s, hs, hx⟩
    exact ⟨_, ⟨⟨s, hs⟩, rfl⟩, ((hSi s hs).isGenericPoint_genericPoint (hSc s hs)).specializes hx⟩

theorem coheight_step {Y : Scheme.{0}} {t x : Y} (h : t ⤳ x) (W : Set Y) (hW : IsOpen W) (ht : t ∈ W)
    (hx : x ∉ W) : Order.coheight t + 1 ≤ Order.coheight x := by
  apply Order.coheight_add_one_le
  exact lt_iff_le_not_ge.2 ⟨h, fun h' => hx (Specializes.mem_open h' hW ht)⟩

section Cot

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

def ev₀ : Sec p (fOpen ι g₀) →+* ℂ := CxPts.evHom hy

def sqQ : Submodule ℂ (Sec p (fOpen ι g₀)) := ((RingHom.ker (ev₀ ι g₀ hy)) ^ 2).restrictScalars ℂ

def rr (l : Fin (N + 1)) : Sec p (fOpen ι g₀) := fRatio ι (MvPolynomial.X l) g₀ (ProjSpace.X_mem ℂ N l) hg₀

def fr (c : Fin (N + 1) → ℂ) : Sec p (fOpen ι g₀) := fRatio ι (lin c) g₀ (lin_mem c) hg₀

def vv (l : Fin (N + 1)) : Sec p (fOpen ι g₀) :=
  rr ι g₀ hg₀ l - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (rr ι g₀ hg₀ l))

def Lm : (Fin (N + 1) → ℂ) →ₗ[ℂ] Sec p (fOpen ι g₀) ⧸ sqQ ι g₀ hy :=
  (sqQ ι g₀ hy).mkQ ∘ₗ Fintype.linearCombination ℂ (vv ι g₀ hg₀ hy)

theorem ev₀_algebraMap (z : ℂ) : ev₀ ι g₀ hy (algebraMap ℂ (Sec p (fOpen ι g₀)) z) = z := by
  first
  | exact (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy z)
  | exact CxPts.ev_algX hy z

theorem ev₀_smul (z : ℂ) (a : Sec p (fOpen ι g₀)) : ev₀ ι g₀ hy (z • a) = z * ev₀ ι g₀ hy a := by
  rw [Algebra.smul_def, map_mul, ev₀_algebraMap]

theorem mkQ_eq_mkQ (a b : Sec p (fOpen ι g₀)) :
    (sqQ ι g₀ hy).mkQ a = (sqQ ι g₀ hy).mkQ b ↔ a - b ∈ RingHom.ker (ev₀ ι g₀ hy) ^ 2 := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Iff.rfl

theorem Lm_apply' (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ (∑ l, c l • vv ι g₀ hg₀ hy l) := by
  simp only [Lm, LinearMap.coe_comp, Function.comp_apply, Fintype.linearCombination_apply]

theorem Lm_apply (hp : ι ≫ PSpace.str ℂ N = p) (c : Fin (N + 1) → ℂ) :
    Lm ι g₀ hg₀ hy c = (sqQ ι g₀ hy).mkQ
      (fr ι g₀ hg₀ c - algebraMap ℂ (Sec p (fOpen ι g₀)) (ev₀ ι g₀ hy (fr ι g₀ hg₀ c))) := by
  rw [Lm_apply']
  have hfr : fr ι g₀ hg₀ c = ∑ l, c l • rr ι g₀ hg₀ l :=
    fRatio_linear X p N ι hp g₀ hg₀ c (lin_mem c)
  rw [hfr]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vv, smul_sub, Finset.sum_sub_distrib, map_sum, ev₀_smul, map_mul, Algebra.smul_def,
    ev₀_algebraMap, mul_sub]

end Cot

section Range

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} (ι : X ⟶ PSpace ℂ N) (g₀ : MvPolynomial (Fin (N + 1)) ℂ)
  (hg₀ : g₀ ∈ ProjSpace.grading ℂ N 1) {y : CxPts p (RingHom.id ℂ)}
  (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (fOpen ι g₀))

end Range

end GlobalTheory.EtProj.Generic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsProjFormNonvanishingGenericPointComplexPoiStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projForm_nonvanishing_genericPoint_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N) (n : ℕ)
    (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  first | (exact @GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (exact GlobalTheory.EtProj.exists_form_genericPoint_cxPts) | (intros; apply GlobalTheory.EtProj.exists_form_genericPoint_cxPts  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteComplexPointsTransversalZerosStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_complexPoints_transversal_zeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ (k : ℕ) (φ : Fin k → Γ(X, U)), {z : CxPts p (RingHom.id ℂ) | ∃ hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U,
      (∀ j, CxPts.evHom hz (φ j) = 0) ∧
        RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range φ) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2}.Finite := by
  first | (exact @GlobalTheory.TransvZeros.finite_transv_zeros) | (exact GlobalTheory.TransvZeros.finite_transv_zeros) | (intros; apply GlobalTheory.TransvZeros.finite_transv_zeros  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalOfFiniteSubringFractionStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  first | (exact @GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (exact GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (intros; apply GlobalTheory.finiteDimensional_of_finite_subring_fraction  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormallyUnramifiedDifferentialsSpan
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_differentials_span : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  first | (exact @GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (exact GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (intros; apply GlobalTheory.W1.dv_mem_span_of_formallyUnramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

end GlobalTheory.W1.Lef
end
end

