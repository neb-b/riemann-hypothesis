module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBasisFgMaximalOrderSpanningFree
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrderBasis

theorem exists_basis_pi {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (s t : E) (hs : IsUnit s) (ht : IsUnit t) :
    ∀ (m : ℕ) (Q : Submodule R (Fin m → E)), (∀ q ∈ Q, ∀ i, s * q i ∈ R) →
      (∀ i, (Pi.single i t : Fin m → E) ∈ Q) →
      ∃ b : Fin m → Fin m → E, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  intro m
  induction m with
  | zero =>
    intro Q _ _
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, Subsingleton.elim _ _⟩
  | succ m ih =>
    intro Q h1 h2
    let I : Ideal R :=
      { carrier := {r | ∃ q ∈ Q, s * q 0 = r}
        add_mem' := by
          rintro a b ⟨p, hp, hpa⟩ ⟨q, hq, hqb⟩
          exact ⟨p + q, Q.add_mem hp hq, by simp [mul_add, hpa, hqb]⟩
        zero_mem' := ⟨0, Q.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨p, hp, hpa⟩
          refine ⟨c • p, Q.smul_mem c hp, ?_⟩
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Subring.coe_mul, ← hpa]
          ring }
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
    obtain ⟨q0, hq0, hq0a⟩ := haI
    have hmul : ∀ q ∈ Q, ∃ c : R, q 0 = c * q0 0 := by
      intro q hq
      have : (⟨s * q 0, h1 q hq 0⟩ : R) ∈ I := ⟨q, hq, rfl⟩
      rw [ha, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨c, hs.mul_left_cancel ?_⟩
      have := congrArg Subtype.val hc
      simp only [smul_eq_mul, Subring.coe_mul] at this
      rw [← this, ← hq0a]; ring
    have hu : IsUnit (q0 0) := by
      obtain ⟨c, hc⟩ := hmul _ (h2 0)
      simp only [Pi.single_eq_same] at hc
      rw [hc] at ht
      exact isUnit_of_mul_isUnit_right ht
    let j : (Fin m → E) →ₗ[E] (Fin (m + 1) → E) :=
      LinearMap.pi (fun i => Fin.cases 0 (fun k => LinearMap.proj k) i)
    have j0 : ∀ v, j v 0 = 0 := fun v => by simp [j]
    have js : ∀ v k, j v (Fin.succ k) = v k := fun v k => by simp [j]
    obtain ⟨b, hb, hQ⟩ := ih (Q.comap (j.restrictScalars R))
      (fun q hq i => by have := h1 _ hq i.succ; simpa [js] using this)
      (fun i => by
        have : j (Pi.single i t) = Pi.single i.succ t := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
          · rw [js]; simp [Pi.single_apply]
        show j (Pi.single i t) ∈ Q
        rw [this]; exact h2 _)
    refine ⟨Fin.cons q0 (fun i => j (b i)), ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hg0 : g 0 = 0 := by
        have := congrFun hg 0
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, j0, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
        exact hu.mul_left_eq_zero.mp this
      have hgs : ∑ i, g (Fin.succ i) • b i = 0 := by
        funext k
        have := congrFun hg k.succ
        simpa [hg0, js, Finset.sum_apply] using this
      intro i
      refine Fin.cases hg0 (fun i => ?_) i
      exact Fintype.linearIndependent_iff.mp hb _ hgs i
    · apply le_antisymm
      · intro q hq
        obtain ⟨c, hc⟩ := hmul q hq
        have hq' : q - c • q0 ∈ Q := Q.sub_mem hq (Q.smul_mem c hq0)
        have he : j (fun k => (q - c • q0) k.succ) = q - c • q0 := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0]; simp [Subring.smul_def, hc]
          · rw [js]
        have hm : (fun k : Fin m => (q - c • q0) k.succ) ∈ Q.comap (j.restrictScalars R) := by
          show j _ ∈ Q
          rw [he]; exact hq'
        rw [hQ] at hm
        have hm2 := Submodule.mem_map_of_mem (f := j.restrictScalars R) hm
        rw [Submodule.map_span] at hm2
        have hm3 : q - c • q0 ∈ Submodule.span R
            (Set.range (Fin.cons q0 (fun i => j (b i)) : Fin (m + 1) → Fin (m + 1) → E)) := by
          rw [← he]
          refine Submodule.span_mono ?_ hm2
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i.succ, by simp⟩
        have : q = (q - c • q0) + c • q0 := by abel
        rw [this]
        exact Submodule.add_mem _ hm3 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases hq0 (fun i => ?_) i
        have : b i ∈ Q.comap (j.restrictScalars R) := by
          rw [hQ]; exact Submodule.subset_span ⟨i, rfl⟩
        simpa using this

theorem exists_common {E : Type} [CommRing E] (R : Subring E) {ι : Type} [Fintype ι]
    (P : ι → E → Prop) (hP : ∀ i d c, c ∈ R → P i d → P i (c * d))
    (h : ∀ i, ∃ d ∈ R, IsUnit d ∧ P i d) : ∃ d ∈ R, IsUnit d ∧ ∀ i, P i d := by
  choose d hdR hdu hd using h
  refine ⟨∏ i, d i, R.prod_mem fun i _ => hdR i, IsUnit.prod_iff.mpr fun i _ => hdu i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP _ _ _ (R.prod_mem fun i _ => hdR i) (hd i)

theorem exists_basis {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (hD : ∀ x : E, ∃ d ∈ R, IsUnit d ∧ d * x ∈ R) {V : Type} [AddCommGroup V] [Module E V]
    {m : ℕ} (y : Fin m → V) (hy : LinearIndependent E y) (Q : Submodule R V) (hQ : Q.FG)
    (hs : Submodule.span E (Q : Set V) = Submodule.span E (Set.range y)) :
    ∃ b : Fin m → V, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  let φ : (Fin m → E) →ₗ[E] V := Fintype.linearCombination E y
  have hφ : Function.Injective φ := hy.fintypeLinearCombination_injective
  have hr : ∀ q ∈ Q, ∃ v, φ v = q := by
    intro q hq
    have : q ∈ Submodule.span E (Set.range y) := hs ▸ Submodule.subset_span hq
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hmap : (Q.comap (φ.restrictScalars R)).map (φ.restrictScalars R) = Q :=
    Submodule.map_comap_eq_self fun q hq => hr q hq
  have hfg : (Q.comap (φ.restrictScalars R)).FG :=
    Submodule.fg_of_fg_map_injective (φ.restrictScalars R) hφ (by rw [hmap]; exact hQ)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  obtain ⟨s, -, hsu, hs1⟩ := exists_common R (fun (p : Fin k × Fin m) d => d * g p.1 p.2 ∈ R)
    (fun p d c hc h => by rw [mul_assoc]; exact R.mul_mem hc h) (fun p => hD _)
  have hsp : ∀ x ∈ Submodule.span E (Q : Set V), ∃ d ∈ R, IsUnit d ∧ d • x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, R.one_mem, isUnit_one, by simpa using hx⟩
    | zero => exact ⟨1, R.one_mem, isUnit_one, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hz⟩ := hz
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (x + z) = (⟨e, he⟩ : R) • d • x + (⟨d, hd⟩ : R) • e • z := by
        simp only [Subring.smul_def, smul_add, smul_smul, mul_comm]
      rw [this]
      exact Q.add_mem (Q.smul_mem _ hx) (Q.smul_mem _ hz)
    | smul c x _ hx =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hc⟩ := hD c
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (c • x) = (⟨e * c, hc⟩ : R) • d • x := by
        simp only [Subring.smul_def, smul_smul]
        congr 1; ring
      rw [this]
      exact Q.smul_mem _ hx
  obtain ⟨t, -, htu, ht1⟩ := exists_common R (fun (i : Fin m) d => d • y i ∈ Q)
    (fun i d c hc h => by rw [mul_smul]; exact Q.smul_mem (⟨c, hc⟩ : R) h)
    (fun i => hsp _ (hs ▸ Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨b, hb, hQb⟩ := exists_basis_pi R s t hsu htu m (Q.comap (φ.restrictScalars R))
    (by
      intro q hq i
      rw [← hg] at hq
      induction hq using Submodule.span_induction with
      | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hs1 (l, i)
      | zero => simp
      | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact R.add_mem hx hz
      | smul c x _ hx =>
        have : s * (c • x) i = c * (s * x i) := by
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
        rw [this]; exact R.mul_mem c.2 hx)
    (fun i => by
      show φ (Pi.single i t) ∈ Q
      simpa [φ, Fintype.linearCombination_apply_single] using ht1 i)
  refine ⟨φ ∘ b, hb.map' φ (LinearMap.ker_eq_bot.mpr hφ), ?_⟩
  rw [← hmap, hQb, Submodule.map_span, Set.range_comp]
  rfl

theorem order_basis : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Q : Submodule L.O (Fin n → E), Q.FG → Submodule.span E (Q : Set (Fin n → E)) = Submodule.span E (Set.range y) → ∃ b : Fin m → Fin n → E, LinearIndependent E b ∧ Q = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m y hy Q hQ hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  refine exists_basis L.O (fun x => ?_) y hy Q hQ hs
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨algebraMap 𝒪[F] E d, (L.O_def _).mpr isIntegral_algebraMap, ?_, (L.O_def _).mpr ?_⟩
  · rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    exact (IsLocalization.map_units F d).map _
  · rwa [Submonoid.smul_def, Algebra.smul_def] at hd

end GlobalTheory.OrderBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatum
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.InnerDatumAct

open Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def FixesFrame (H : HermSp M V) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop :=
  IsUnitary H g ∧ ∀ b, g (f b) = f b

lemma FixesFrame.symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    FixesFrame H f g.symm := by
  refine ⟨fun x y => ?_, fun b => ?_⟩
  · have := hg.1 (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rw [LinearEquiv.symm_apply_eq, hg.2 b]

lemma FixesFrame.mem_X {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.X f) : g v ∈ H.X f := by
  have hle : H.X f ≤ (H.X f).comap (g : V →ₗ[E] V) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hg.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact hle hv

lemma FixesFrame.mem_perp {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' := hg.symm.mem_X hx
  have h1 := hg.1 v (g.symm x)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact (hv : ∀ x ∈ H.X f, H.h v x = 0) _ hx'

def perpMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    ↥(H.perp (H.X f)) →ₗ[E] ↥(H.perp (H.X f)) :=
  (g : V →ₗ[E] V).restrict (fun _ hv => hg.mem_perp hv)

def wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) : H.Wb f →ₗ[E] H.Wb f :=
  Submodule.mapQ _ _ (perpMap hg) (fun x hx => by
    show ((perpMap hg x : ↥(H.perp (H.X f))) : V) ∈ H.X f
    exact hg.mem_X hx)

lemma wMap_mk {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (x : ↥(H.perp (H.X f))) : wMap hg (H.mkW f x) = H.mkW f ⟨g x, hg.mem_perp x.2⟩ := rfl

lemma mkW_congr {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) = y) :
    H.mkW f x = H.mkW f y := by
  rw [Subtype.ext h]

lemma wMap_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg (H.mkW f x) = H.mkW f y := by
  rw [wMap_mk]; exact mkW_congr h.symm

lemma wMap_symm_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg.symm (H.mkW f y) = H.mkW f x := by
  rw [wMap_mk]; apply mkW_congr; simp [h]

lemma wMap_symm_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg.symm (wMap hg w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  exact (congrArg (wMap hg.symm) (wMap_of_eq hg (y := ⟨g x, hg.mem_perp x.2⟩) rfl)).trans
    (wMap_symm_of_eq hg rfl)

lemma wMap_wMap_symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg (wMap hg.symm w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  have e : (x : V) = g (g.symm x) := by simp
  exact (congrArg (wMap hg) (wMap_symm_of_eq hg (x := ⟨g.symm x, hg.symm.mem_perp x.2⟩) e)).trans
    (wMap_of_eq hg e)

lemma mem_map_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (L : Submodule M.L.O (H.Wb f)) (w : H.Wb f) :
    w ∈ L.map ((wMap hg).restrictScalars M.L.O) ↔ wMap hg.symm w ∈ L := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show wMap hg.symm (wMap hg u) ∈ L
    rw [wMap_symm_wMap]; exact hu
  · intro h
    exact ⟨_, h, wMap_wMap_symm hg w⟩

def InU (P : FPair H r) (g : V ≃ₗ[E] V) : Prop := FixesFrame H P.A.f g ∧ FixesFrame H P.B.f g

lemma inU_of_mem {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) : InU P g := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨⟨hx.1, fun b => (hx.2 b).1⟩, ⟨hx.1, fun b => (hx.2 b).2⟩⟩
  | one => exact ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨⟨fun a b => ?_, fun b => ?_⟩, ⟨fun a b => ?_, fun b => ?_⟩⟩ <;>
      simp only [LinearEquiv.mul_apply]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.1.2, hx.1.2]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.2.2, hx.2.2]
  | inv x _ hx => exact ⟨hx.1.symm, hx.2.symm⟩

lemma isInner_map (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : FixesFrame H Fr.f g)
    {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) :
    Fr.IsInner (L.map ((wMap hg).restrictScalars M.L.O)) := by
  obtain ⟨hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : g.symm xz = xz := by
    rw [hxz]; exact hg.symm.2 (Fin.last r)
  refine ⟨hfg.map _, fun x => ?_, xz, hxz, ?_, fun c y hy heq => ?_⟩
  · rw [mem_map_wMap, wMap_mk, hdual]
    constructor
    · intro h y hy
      rw [mem_map_wMap, wMap_mk] at hy
      have h1 := h _ hy
      have h2 := hg.symm.1 x y
      simp only at h1
      rw [h2] at h1
      exact h1
    · intro h y hy
      have hy' : H.mkW Fr.f ⟨g y, hg.mem_perp y.2⟩ ∈ L.map ((wMap hg).restrictScalars M.L.O) := by
        rw [mem_map_wMap, wMap_symm_of_eq hg rfl]; exact hy
      have h1 := h _ hy'
      have h2 := hg.symm.1 x (g y)
      simp only [LinearEquiv.symm_apply_apply] at h2
      show H.h (g.symm x) y ∈ M.L.O
      rw [h2]; exact h1
  · rw [mem_map_wMap, wMap_mk]
    rw [mkW_congr (y := xz) hz]; exact hxzL
  · rw [mem_map_wMap] at hy
    refine hprim c ⟨g.symm y, hg.symm.mem_perp y.2⟩ ?_ ?_
    · rw [← wMap_mk]; exact hy
    · have h3 := congrArg (wMap hg.symm) heq
      rw [LinearMap.map_smul, wMap_mk, wMap_mk, mkW_congr (y := xz) hz] at h3
      exact h3

def act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) : Datum P where
  L := d.L.map ((wMap hg.1).restrictScalars M.L.O)
  L' := d.L'.map ((wMap hg.2).restrictScalars M.L.O)
  hL := isInner_map P.A hg.1 d.hL
  hL' := isInner_map P.B hg.2 d.hL'
  io := {p | (wMap hg.2.symm p.1, wMap hg.1.symm p.2) ∈ d.io}
  io_L := fun h => by
    ext p
    simp [d.io_L h]

lemma datum_ext {P : FPair H r} {d₁ d₂ : Datum P} (hL : d₁.L = d₂.L) (hL' : d₁.L' = d₂.L')
    (hio : d₁.io = d₂.io) : d₁ = d₂ := by
  cases d₁; cases d₂
  simp only at hL hL' hio
  subst hL hL' hio
  rfl

lemma moves_act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) :
    Datum.Moves g d (act hg d) := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · show _ ↔ _ ∈ d.L.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.1 hxy]
  · show _ ↔ _ ∈ d.L'.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.2 hxy]
  · show _ ↔ (wMap hg.2.symm _, wMap hg.1.symm _) ∈ d.io
    rw [wMap_symm_of_eq hg.2 hx', wMap_symm_of_eq hg.1 hx]

lemma moves_unique {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) {d d₁ d₂ : Datum P}
    (h₁ : Datum.Moves g d d₁) (h₂ : Datum.Moves g d d₂) : d₁ = d₂ := by
  refine datum_ext ?_ ?_ ?_
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.1 ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e)
  · ext w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e).symm.trans
      (h₂.2.1 ⟨g.symm y, hg.2.symm.mem_perp y.2⟩ y e)
  · ext ⟨w', w⟩
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ w'
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ w
    have e' : (y' : V) = g (g.symm y') := by simp
    have e : (y : V) = g (g.symm y) := by simp
    exact (h₁.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y' ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y
      e' e).symm.trans (h₂.2.2 ⟨g.symm y', hg.2.symm.mem_perp y'.2⟩ y'
        ⟨g.symm y, hg.1.symm.mem_perp y.2⟩ y e' e)

lemma moves_one {P : FPair H r} (d : Datum P) : Datum.Moves (1 : V ≃ₗ[E] V) d d := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hx, Subtype.ext hx']

lemma moves_comp {P : FPair H r} {g g' : V ≃ₗ[E] V} (hg : InU P g) {d₁ d₂ d₃ : Datum P}
    (h₁₂ : Datum.Moves g d₁ d₂) (h₂₃ : Datum.Moves g' d₂ d₃) : Datum.Moves (g' * g) d₁ d₃ := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · exact (h₁₂.1 x ⟨g x, hg.1.mem_perp x.2⟩ rfl).trans
      (h₂₃.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.1 x ⟨g x, hg.2.mem_perp x.2⟩ rfl).trans
      (h₂₃.2.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.2 x' ⟨g x', hg.2.mem_perp x'.2⟩ x ⟨g x, hg.1.mem_perp x.2⟩ rfl rfl).trans
      (h₂₃.2.2 _ y' _ y (by rw [hx', LinearEquiv.mul_apply]) (by rw [hx, LinearEquiv.mul_apply]))

theorem exists_mulAction : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _
  let sm : P.UW0 → Datum P → Datum P := fun g d => act (inU_of_mem g.2) d
  have key : ∀ (g : P.UW0) d d', Datum.Moves g.1 d d' ↔ sm g d = d' := fun g d d' =>
    ⟨fun h => moves_unique (inU_of_mem g.2) (moves_act _ d) h, fun h => h ▸ moves_act _ d⟩
  letI act' : MulAction P.UW0 (Datum P) :=
    { smul := sm
      one_smul := fun d => (key 1 d d).1 (moves_one d)
      mul_smul := fun g g' d => (key (g * g') d _).1
        (moves_comp (inU_of_mem g'.2) ((key g' d _).2 rfl) ((key g _ _).2 rfl)) }
  refine ⟨act', key, fun d g => ?_⟩
  have hS : Datum.Stab d = (MulAction.stabilizer P.UW0 d).map P.UW0.subtype := by
    unfold Datum.Stab
    have hset : {g | g ∈ P.UW0 ∧ Datum.Moves g d d} =
        ((MulAction.stabilizer P.UW0 d).map P.UW0.subtype : Set (V ≃ₗ[E] V)) := by
      ext g
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map, MulAction.mem_stabilizer_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, hg⟩, (key ⟨g, hg⟩ d d).1 hm, rfl⟩
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, (key g' d d).2 hg'⟩
    rw [hset, Subgroup.closure_eq]
  rw [hS, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := Subtype.ext he
    subst this
    exact MulAction.mem_stabilizer_iff.1 hg'
  · intro h
    exact ⟨g, MulAction.mem_stabilizer_iff.2 h, rfl⟩

end GlobalTheory.InnerDatumAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndepOfGqNeZero
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Iota

variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
  simpa using h


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.SgGlob.Iota.one_mem_dInv (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)

section Pair

variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}

end Pair

section Gram

end Gram

end GlobalTheory.SgGlob.Iota
end
end

