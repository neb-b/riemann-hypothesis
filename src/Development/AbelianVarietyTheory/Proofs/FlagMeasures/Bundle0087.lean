module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteClasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThickOrbitSelfDualUnramifiedLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBounds
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unfold

open GlobalTheory.HL.TracePart

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem smul_inf_eq {Y : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hh : h ∈ fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (h • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by
  have hi := ((fixG L Hm Y).inv_mem hh).2.2
  ext v
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  refine and_congr_left fun hv => ?_
  have := hi v hv
  rw [Submodule.mem_bot, sub_eq_zero] at this
  rw [this]

theorem image_thick (ϖ : 𝒪[F]) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm)
    (Λ : Submodule L.O (Fin n → E)) (x : Fin m → Fin n → E) (i : ℕ) :
    (fun x a => g (x a)) '' thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) fun a => g⁻¹ (x a)) i =
      thick L ϖ (torb (isomG L Hm ⊓ stabL L (g • Λ)) x) i := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨g * k * g⁻¹, ⟨?_, ?_⟩, rfl⟩, A, hA, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg hk.1) ((isomG L Hm).inv_mem hg)
    · have h2 : k • Λ = Λ := hk.2
      show (g * k * g⁻¹) • g • Λ = g • Λ
      rw [mul_smul, mul_smul, inv_smul_smul, h2]
    · exact map_rmul g _ A
  · rintro ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩
    refine ⟨_, ⟨_, ⟨g⁻¹ * k * g, ⟨?_, ?_⟩, rfl⟩, A, hA, rfl⟩, ?_⟩
    · exact (isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg) hk.1) hg
    · have h2 : k • g • Λ = g • Λ := hk.2
      show (g⁻¹ * k * g) • Λ = Λ
      rw [mul_smul, mul_smul, h2, inv_smul_smul]
    · refine (map_rmul g _ A).trans ?_
      congr 1
      funext a
      have e1 : ∀ v, g (g⁻¹ v) = v := fun v => g.apply_symm_apply v
      show g (g⁻¹ (k (g (g⁻¹ (x a))))) = k (x a)
      rw [e1, e1]

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem sigMass_eq_sum (hH : IsHermND L Hm) {Λs : Submodule L.O (Fin n → E)} (hs : IsSD L Hm Λs)
    (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) {Λ0 : Submodule L.O (Fin n → E)}
    (h0 : IsLat L Λ0) (Mh : Submodule L.O (Fin n → E))
    (s : Finset ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    (h1 : ∀ g ∈ s, g ∈ isomG L Hm ∧
      (g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh)
    (h2 : ∀ Λ, IsSD L Hm Λ → Λ ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Mh →
      ∃! g, g ∈ s ∧ ∃ h ∈ fixG L Hm (Submodule.span E (Set.range x)), Λ = h • g • Λs) :
    sigMass L Hm (Submodule.span E (Set.range x)) Λ0 Mh =
      ENNReal.ofReal (∑ g ∈ s, invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs))) := by
  set Y := Submodule.span E (Set.range x) with hY
  let φ : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →
      MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)) :=
    fun g => Quotient.mk _ (g • Λs)
  have hout : ∀ g, ∃ h ∈ fixG L Hm Y, (φ g).out = h • g • Λs := by
    intro g
    have : (MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (φ g).out (g • Λs) :=
      Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm Y) (Submodule L.O (Fin n → E))) (g • Λs)
    obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.1 this
    exact ⟨h.1, h.2, hh.symm⟩
  have hinj : ∀ g ∈ s, ∀ g' ∈ s, φ g = φ g' → g = g' := by
    intro g hg g' hg' e
    obtain ⟨h, hh, e1⟩ := hout g
    obtain ⟨h', hh', e2⟩ := hout g'
    have hsd : IsSD L Hm (φ g).out := by
      rw [e1]; exact isSD_smul hh.1 (isSD_smul (h1 g hg).1 hs)
    have htr : (φ g).out ⊓ Y.restrictScalars L.O = Mh := by
      rw [e1, smul_inf_eq hh, (h1 g hg).2]
    exact (h2 _ hsd htr).unique ⟨hg, h, hh, e1⟩ ⟨hg', h', hh', e ▸ e2⟩
  rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => by unfold invVol; positivity)]
  unfold sigMass
  rw [tsum_eq_sum (s := s.image φ), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun g hg => ?_
    obtain ⟨h, hh, e1⟩ := hout g
    have hsd := isSD_smul (h1 g hg).1 hs
    rw [e1, if_pos ⟨isSD_smul hh.1 hsd, by rw [smul_inf_eq hh, (h1 g hg).2]⟩,
      GlobalTheory.HL.Unimod.unimodular L Hm hH m x hx Λ0 _ h0 hsd.1 h hh]
  · intro o ho
    rw [if_neg]
    rintro ⟨hsd, htr⟩
    obtain ⟨g, ⟨hg, h, hh, e⟩, -⟩ := h2 _ hsd htr
    refine ho (Finset.mem_image.2 ⟨g, hg, ?_⟩)
    rw [← Quotient.out_eq o]
    refine (Quotient.sound ?_).symm
    exact MulAction.orbitRel_apply.2 ⟨⟨h, hh⟩, e.symm⟩

theorem mass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ENNReal.ofReal (κ / 2 * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) ≤ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ sigMass L Hm (Submodule.span E (Set.range x)) Λ0 (Submodule.span L.O (Set.range (rmul x A⁻¹))) ≤ ENNReal.ofReal (2 * κ * (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)))) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx hmn Λ0 h0
  obtain ⟨κ, hκ, hk⟩ := GlobalTheory.HL.QuotMass.mass_eq_const_mul_content L ϖ hϖ Hm hH Λs hs m x hx Λ0 h0
  refine ⟨κ, hκ, fun A hA hint => ?_⟩
  obtain ⟨s, h1, h2, i1, h3⟩ := trace_partition L ϖ hϖ Hm hH Λs hs m x hx A hA
  obtain ⟨i2, h4⟩ := GlobalTheory.PrimScale.cont_prim_scale L ϖ hϖ Hm hH Λs hs m x hx hmn A hA hint
  rw [sigMass_eq_sum hH hs x hx h0 _ s h1 h2]
  have hg : ∀ g, ∃ j : ℕ, g ∈ s → ∀ i ≥ j,
      IsCO (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) ∧
      invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0)
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (g • Λs)) *
        cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) = κ * cont (tupLat L Λs m)
          (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) := by
    intro g
    by_cases hgs : g ∈ s
    swap
    · exact ⟨0, fun h => absurd h hgs⟩
    have hgi := (h1 g hgs).1
    obtain ⟨j1, hj1⟩ := hk _ (isSD_smul hgi hs)
    obtain ⟨e, he⟩ := GlobalTheory.HL.QuotMass.exists_pow_smul L ϖ hϖ hs.1 (fun a => g⁻¹ (x a))
    obtain ⟨j2, -, hj2⟩ := GlobalTheory.ThickOrbit.main L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e
    refine ⟨max j1 j2, fun _ i hi => ?_⟩
    have hco := (hj2 i (le_of_max_le_right hi) (isomG L Hm ⊓ stabL L Λs) le_rfl
      (fun k hk hk' => ⟨hk, (GlobalTheory.HL.congruence_subgroup_facts L ϖ hϖ Λs hs.1 1).2.1 le_rfl k hk'⟩)
      (fun a => g⁻¹ (x a)) he (gramT_isom ((isomG L Hm).inv_mem hgi) x)).1
    refine ⟨hco, ?_⟩
    rw [hj1 i (le_of_max_le_left hi), ← image_thick ϖ hgi,
      ((GlobalTheory.HL.TupleJac.tuple_jacobian L ϖ hϖ Hm hH Λs hs m).2 g hgi _ hco).2]
  choose j hj using hg
  set i := max (max (max i1 i2) 1) (s.sup j) with hi
  have hij : ∀ g ∈ s, j g ≤ i := fun g hg => (Finset.le_sup hg).trans (le_max_right _ _)
  obtain ⟨hU, hD⟩ := h3 i (by omega)
  obtain ⟨hl, hu⟩ := h4 i (by omega)
  have hherm : IsHerm L (gramT L Hm x) := by
    funext a b
    exact (GlobalTheory.HL.Unimod.hf_swap L hH.1 _ _).symm
  have hpos := ((GlobalTheory.CongGrp.congK_group L ϖ hϖ m i (by omega)).2.2 _ hherm hx).2
  have hsum := (GlobalTheory.HL.cont_biUnion (tupLat L Λs m) s _
    (fun g hg => (hj g hg i (hij g hg)).1)).2 hD
  rw [hU, hsum] at hl hu
  have key := Finset.sum_congr rfl fun g (hg : g ∈ s) => (hj g hg i (hij g hg)).2
  rw [← Finset.sum_mul, ← Finset.mul_sum] at key
  constructor
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hl hκ.le
    linarith
  · refine ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right ?_ hpos)
    rw [key]
    have := mul_le_mul_of_nonneg_left hu hκ.le
    linarith

end GlobalTheory.HL.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumClsLeEncard
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassCount

theorem tsum_le_encard {G X : Type*} [Group G] [MulAction G X] (H K0 : Subgroup G) (hK : K0 ≤ H)
    (P Q : X → Prop) (w : X → ℝ)
    (hP : ∀ x, P x → ∃ h ∈ H, w x = invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) ∧
      H ⊓ MulAction.stabilizer G (h • x) ≤ K0 ∧ ∀ k ∈ K0, Q (k • h • x)) :
    (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (w o.out) * 1 else 0)
      ≤ (({x | Q x} : Set X).encard : ℝ≥0∞) := by
  rw [encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X)) Q]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  swap
  · exact zero_le
  obtain ⟨h, hh, hw, hle, hQ⟩ := hP _ ho
  have h2 : (H ⊓ MulAction.stabilizer G (h • o.out)).relIndex K0
      = (MulAction.orbit K0 (h • o.out)).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hK hg, a⟩⟩
  have h3 : MulAction.orbit K0 (h • o.out) ⊆
      {x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ Q x} := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨?_, hQ g hg⟩
    conv_rhs => rw [← Quotient.out_eq' o]
    rw [Quotient.eq'', MulAction.orbitRel_apply]
    exact ⟨⟨g * h, mul_mem (hK hg) hh⟩, mul_smul g h o.out⟩
  rw [hw, invVol, Subgroup.relIndex_eq_one.2 hle, h2, Nat.cast_one, div_one, mul_one,
    ENNReal.ofReal_natCast]
  have h4 : ((MulAction.orbit K0 (h • o.out)).ncard : ℕ∞) ≤ _ :=
    (Set.ncard_le_encard _).trans (Set.encard_le_encard h3)
  exact_mod_cast h4

theorem sameBlock_trans {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∀ a b c : ℕ, sameBlock bs a b = true → sameBlock bs a c = true → sameBlock bs b c = true := by
  induction bs with
  | nil => intro a b c h; simp [sameBlock] at h
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro a b c h1 h2
    simp only [sameBlock, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact Or.inl ⟨h1.2, h2.2⟩
    · omega
    · omega
    · exact Or.inr ⟨⟨h1.2, h2.2⟩, ih _ _ _ h1' h2'⟩

theorem isUni_mul {E : Type} [CommRing E] {N : ℕ} {s u : Matrix (Fin N) (Fin N) E}
    (hs : IsUni s) (hu : IsUni u) : IsUni (s * u) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hs.1 i l h, zero_mul]
    · rw [hu.1 l j (hij.trans_le h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hs.2, hu.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hs.1 i l h, zero_mul]
      · rw [hu.1 l i h, mul_zero]
    · simp

theorem apply_frame {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {N : ℕ}
    (g : V ≃ₗ[E] V) (f : Fin N → V) (s u : Matrix (Fin N) (Fin N) E)
    (hs : ∀ j, g (f j) = ∑ i, s i j • f i) (j : Fin N) :
    g (∑ i, u i j • f i) = ∑ i, (s * u) i j • f i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hs, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem smul_span (g : S.GLV) (f : Fin (r + 1) → S.V) :
    g • Submodule.span L.O (Set.range f) = Submodule.span L.O (Set.range fun b => g (f b)) := by
  rw [Submodule.smul_span, ← Set.image_smul, ← Set.range_comp]
  rfl

theorem isIntCls_smul {h : S.GLV} (hh : h ∈ S.St) {C : Set S.FrP} (hC : S.IsIntCls C) :
    S.IsIntCls (h • C) := by
  obtain ⟨⟨n, hn, n', hn', rfl⟩, hI⟩ := hC
  refine ⟨⟨h * n, mul_mem hh.1 hn, h * n', mul_mem hh.2 hn', ?_⟩, ?_⟩
  · rw [(_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.2 h]
    rfl
  · rintro _ ⟨p, hp, rfl⟩ a b
    have := hh.1.1.1 (p.2 b) (p.1 a)
    have h2 := hI p hp a b
    rw [Frames.h, ← this] at h2
    exact h2

theorem span_le_of_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    Submodule.span L.O (Set.range p.1) ≤ Submodule.span L.O (Set.range g) := by
  obtain ⟨A, A', hA, -, -, -, -, h1, -⟩ := hp
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  rw [h1 j]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ (⟨A i j, hA i j⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)

theorem stab_le (g g' : Fin (r + 1) → S.V) :
    MulAction.stabilizer S.GLV (S.frameCls g g') ≤ stabL L (Submodule.span L.O (Set.range g)) := by
  intro h hh
  have h1 : h • S.frameCls g g' = S.frameCls g g' := hh
  rw [(_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.2 h] at h1
  change h • Submodule.span L.O (Set.range g) = _
  rw [smul_span]
  refine le_antisymm ?_ ?_
  · exact span_le_of_mem S (p := (_, _)) (h1 ▸ (_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).1)
  · exact span_le_of_mem S (p := (g, g')) (h1.symm ▸ (_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).1)

theorem matrix_of_mem {g : S.GLV} (hg : g ∈ S.K0) :
    ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s ∧ IsUni s' ∧ IsIntM L s ∧
      (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) ∧
      (∀ j, g (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, g (S.f' j) = ∑ i, s' i j • S.f' i := by
  obtain ⟨s, hs, e⟩ := (FrameOnto.unipotent_onto L r k S).1 g hg.1.1.1
  obtain ⟨s', hs', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 g hg.1.1.2
  have hz := ((_root_.GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨g, hg.1.1, e, e'⟩
  have hb := ((_root_.GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' hz).1
  refine ⟨s, s', hs, hs', fun i j => ?_, fun i j h => (hb i j h).1, e, e'⟩
  have h1 : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hg.1.2
  rw [smul_span] at h1
  have h2 : g (S.f j) ∈ Submodule.span L.O (Set.range S.f) :=
    h1 ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have li : LinearIndependent E S.f :=
    (GlobalTheory.FrameBasic.main L r k S).1.comp Sum.inl Sum.inl_injective
  have h3 := Fintype.linearIndependent_iff.1 li (fun i => s i j - c i) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← e j, ← hc]
    exact sub_self _) i
  rw [sub_eq_zero.1 h3]
  exact (c i).2

end

theorem sumCls_le_encard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (S.sumCls fun _ => 1) ≤ ({C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i}.encard : ℝ≥0∞) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine tsum_le_encard S.St S.K0 (fun _ h => h.1.1) S.IsIntCls _ S.wC fun C hC => ?_
  have hC' := hC
  obtain ⟨⟨n, hn, n', hn', rfl⟩, -⟩ := hC'
  obtain ⟨h, hh, hle, u, hu, hub, e⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
  obtain ⟨u', hu', e'⟩ := (FrameOnto.unipotent_onto L r k S).2.1 (h⁻¹ * n')
    (S.N'.mul_mem (S.St.inv_mem hh).2 hn')
  refine ⟨h⁻¹, inv_mem hh, (((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 _ hC.1).2.2.2 _ (inv_mem hh)).symm, ?_, ?_⟩
  · rintro g ⟨g1, g2⟩
    have h1 : h * g * h⁻¹ ∈ MulAut.conj h • S.K0 := by
      refine hle ⟨S.St.mul_mem (S.St.mul_mem hh g1) (S.St.inv_mem hh), stab_le S _ (fun b => n' (S.f' b)) ?_⟩
      have g3 : g • h⁻¹ • _ = h⁻¹ • _ := g2
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, g3, smul_inv_smul]
    exact (Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj h) (x := g)).1 h1
  · intro g hg
    obtain ⟨s, s', hs, hs', hi, hb, d, d'⟩ := matrix_of_mem S hg
    refine ⟨isIntCls_smul S hg.1.1 (isIntCls_smul S (S.St.inv_mem hh) hC), s * u, s' * u',
      isUni_mul hs hu, isUni_mul hs' hu', fun i j hij => ?_, ?_⟩
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun l _ => ?_
      cases hl : sameBlock S.w.blocks i l
      · rw [hb i l hl, zero_mul]; exact zero_mem _
      · exact mul_mem (hi i l) (hub l j (sameBlock_trans _ _ _ _ hl hij))
    · rw [(_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.2 h⁻¹, (_root_.GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.2 g]
      congr 1
      · funext j
        rw [e j, apply_frame g S.f s u d]
      · funext j
        rw [← apply_frame g S.f' s' u' d', ← e' j]
        rfl

end GlobalTheory.HL.ClassCount
end

