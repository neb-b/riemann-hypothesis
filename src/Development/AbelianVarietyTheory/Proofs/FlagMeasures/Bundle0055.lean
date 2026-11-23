module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

def hq {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := ∑ i, ∑ j, x i * Hm i j * sig (y j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_add_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (a + b) y = _root_.GlobalTheory.HL.SAN.hq sig Hm a y + _root_.GlobalTheory.HL.SAN.hq sig Hm b y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_smul_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (c • a) y = c * _root_.GlobalTheory.HL.SAN.hq sig Hm a y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def eQ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun v := v + hq sig Hm v u • x - hq sig Hm v x • (u + s • x)
  map_add' a b := by
    simp only [hq_add_l]; module
  map_smul' c a := by
    simp only [hq_smul_l, RingHom.id_apply]; module

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.mem_coord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} (x : Fin N → E) :
    x ∈ Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin N → E)) ↔ ∀ j, x j ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · subst h; simp [L.O.one_mem]
      · simp [Pi.single_apply, h, L.O.zero_mem]
    | zero => intro j; exact L.O.zero_mem
    | add y z _ _ hy hz => intro j; exact add_mem (hy j) (hz j)
    | smul c y _ hy =>
      intro j
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hy j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : L.O) • (Pi.single j 1 : Fin N → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem hf_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x y : Fin N → E} (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    hf L Hm x y ∈ L.O :=
  L.O.sum_mem fun i _ => L.O.sum_mem fun j _ =>
    L.O.mul_mem (L.O.mul_mem (hx i) (hI i j)) (GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem hf_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) (x y : Fin n → E) (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    _root_.GlobalTheory.HL.hf L H x y ∈ L.O := by
  unfold _root_.GlobalTheory.HL.hf
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hx i) (hI i j)) (_root_.GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem eich_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) {x u : Fin n → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) {v : Fin n → E} (hv : ∀ j, v j ∈ L.O) (j : Fin n) :
    _root_.GlobalTheory.HL.eich L H x u s v j ∈ L.O := by
  unfold _root_.GlobalTheory.HL.eich
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sub_mem (add_mem (hv j) (mul_mem (hf_mem_O L hI v u hv hu) (hx j)))
    (mul_mem (hf_mem_O L hI v x hv hx) (add_mem (hu j) (mul_mem hs (hx j))))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.int_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by
  intro m
  induction m with
  | zero =>
    intro X u s e _ _ _ _ x hx j
    simpa using hx j
  | succ m ih =>
    intro X u s e hX hu hs he x hx j
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, he 0]
    exact eich_mem_O L hI (hX 0) (hu 0) (hs 0)
      (fun j' => ih (fun i => X i.succ) (fun i => u i.succ) (fun i => s i.succ) (fun i => e i.succ)
        (fun i => hX i.succ) (fun i => hu i.succ) (fun i => hs i.succ) (fun i => he i.succ) x hx j') j

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.ext_prod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ} : ∀ (m : ℕ)
    (a : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (b : Fin m → (Fin N → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin N → (A.loc p).Ep)),
    (∀ i, A.Ext p (a i) (b i)) →
      A.Ext p (List.ofFn a).prod (List.ofFn b).prod := by
  intro m
  induction m with
  | zero =>
    intro a b _
    simp only [_root_.GlobalTheory.HL.Places.Ext]
    intro x
    simp
  | succ m ih =>
    intro a b h
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
    simp only [_root_.GlobalTheory.HL.Places.Ext] at h ih' ⊢
    intro x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, ih', h 0]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.bc_eQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by
  have h5 := (_root_.GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm
  have hu := h5 v u
  have hx := h5 v x
  unfold _root_.GlobalTheory.HL.eich
  rw [hu, hx]
  funext i
  simp [_root_.GlobalTheory.HL.Places.bc, _root_.GlobalTheory.HL.SAN.eQ, _root_.GlobalTheory.HL.SAN.hq]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField F)).ne'⟩⟩

end GlobalTheory.HL.SAN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfIntegral
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem stab_span_of_integral {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : S.GLV)
    (g : Fin (r + 1) → S.V) (s si : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ i j, s i j ∈ L.O) (hsi : ∀ i j, si i j ∈ L.O) (hm : s * si = 1)
    (hg : ∀ j, h (g j) = ∑ i, s i j • g i) :
    h ∈ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range g)) := by
  rw [MulAction.mem_stabilizer_iff]
  set N := Submodule.span L.O (Set.range g) with hN
  have mem : ∀ (c : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, c i j ∈ L.O) →
      ∀ j, ∑ i, c i j • g i ∈ N := by
    intro c hc j
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i j • g i = (⟨c i j, hc i j⟩ : L.O) • g i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rw [Submodule.pointwise_smul_def, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show h (g j) ∈ N
    rw [hg j]
    exact mem s hs j
  · rw [hN, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have key : g j = h (∑ i, si i j • g i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_smul, hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ x, ∑ i, si i j * s x i = (s * si) x j := fun x => by
        rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.smul_mem_pointwise_smul _ h _ (mem si hsi j)

theorem mem_K0_of_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (h : S.GLV) (s si s' si' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), h ∈ S.St → (∀ i j, s i j ∈ L.O) → (∀ i j, si i j ∈ L.O) → s * si = 1 → (∀ i j, s' i j ∈ L.O) → (∀ i j, si' i j ∈ L.O) → s' * si' = 1 → (∀ j, h (S.f j) = ∑ i, s i j • S.f i) → (∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) → h ∈ S.K0 := by
  intro F _ _ _ E _ _ _ L r k S h s si s' si' hSt hs hsi hm hs' hsi' hm' hg hg'
  unfold Frames.K0
  exact ⟨⟨hSt, S.stab_span_of_integral h S.f s si hs hsi hm hg⟩,
    S.stab_span_of_integral h S.f' s' si' hs' hsi' hm' hg'⟩

end GlobalTheory.HL.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanOfMemMof
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PrimTerm

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  unfold Frames.spanTo
  congr 1
  ext x
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩

theorem left_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) : g b ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inl ⟨b, rfl⟩)

theorem diff_mem (g g' : Fin (r + 1) → S.V) (b : Fin (r + 1)) :
    algebraMap F E S.th⁻¹ • (g' b - g b) ∈ S.Mof g g' :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem th_smul (h0 : S.th ≠ 0) (v : S.V) :
    algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
  rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]

theorem Mof_le_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g ≤ S.Mof g g' := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · have h1 := (S.Mof g g').smul_mem ⟨_, hO⟩ (diff_mem S g g' b)
    have h2 : (⟨_, hO⟩ : L.O) • algebraMap F E S.th⁻¹ • (g' b - g b) = g' b - g b :=
      th_smul S h0 _
    rw [h2] at h1
    have h3 := (S.Mof g g').add_mem h1 (left_mem S g g' b)
    rwa [sub_add_cancel] at h3
  · have h1 := (S.Mof g g').neg_mem (diff_mem S g g' b)
    rw [← smul_neg, neg_sub] at h1
    exact h1

theorem Mof_swap (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g = S.Mof g g' :=
  le_antisymm (Mof_le_swap S h0 hO g g') (Mof_le_swap S h0 hO g' g)

theorem mem_span_of_mem_Mof (P P' : Submodule E S.V) (hd : Disjoint P P')
    (g g' : Fin (r + 1) → S.V) (hg : ∀ b, g b ∈ P) (hg' : ∀ b, g' b ∈ P')
    (hi : LinearIndependent E g') (x : S.V) (hx : x ∈ S.Mof g g') (hP : x ∈ P) :
    x ∈ Submodule.span L.O (Set.range g) := by
  unfold Frames.Mof at hx
  rw [Submodule.span_union] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hz
  have hyP : y ∈ P := by
    have : Submodule.span L.O (Set.range g) ≤ P.restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact hg b
    exact this hy
  set e : Fin (r + 1) → E := fun b => (c b : E) * algebraMap F E S.th⁻¹ with he
  have hs : ∑ b, c b • algebraMap F E S.th⁻¹ • (g' b - g b) = ∑ b, e b • g' b - ∑ b, e b • g b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_sub, he, mul_smul]
    rfl
  rw [hs] at hP ⊢
  have h1 : ∑ b, e b • g b ∈ P := P.sum_mem fun b _ => P.smul_mem _ (hg b)
  have h2 : ∑ b, e b • g' b ∈ P' := P'.sum_mem fun b _ => P'.smul_mem _ (hg' b)
  have h3 : ∑ b, e b • g' b ∈ P := by
    have := P.add_mem (P.sub_mem hP hyP) h1
    rwa [add_sub_cancel_left, sub_add_cancel] at this
  have h4 : ∑ b, e b • g' b = 0 := (Submodule.disjoint_def.1 hd) _ h3 h2
  have h5 : ∀ b, e b = 0 := Fintype.linearIndependent_iff.1 hi e h4
  simpa [h5] using hy

theorem trace_iff (Λ : Submodule L.O S.V) (f f' g g' : Fin (r + 1) → S.V)
    (hd : Disjoint (Submodule.span E (Set.range f)) (Submodule.span E (Set.range f')))
    (hg : ∀ b, g b ∈ Submodule.span E (Set.range f))
    (hg' : ∀ b, g' b ∈ Submodule.span E (Set.range f'))
    (hi : LinearIndependent E g') (hME : S.spanTo f (r + 1) ≤ S.ME) (hs : S.sat Λ = S.Mof g g')
    (x : S.V) : (x ∈ Λ ∧ x ∈ S.spanTo f (r + 1)) ↔ x ∈ Submodule.span L.O (Set.range fun b => g b) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : x ∈ S.sat Λ := ⟨h1, hME h2⟩
    rw [hs] at h3
    rw [spanTo_top] at h2
    exact mem_span_of_mem_Mof S _ _ hd g g' hg hg' hi x h3 h2
  · intro hx
    have : Submodule.span L.O (Set.range fun b => g b) ≤
        Λ ⊓ (S.spanTo f (r + 1)).restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have h1 : g b ∈ S.sat Λ := hs ▸ left_mem S g g' b
      refine ⟨h1.1, ?_⟩
      change g b ∈ S.spanTo f (r + 1)
      rw [spanTo_top]
      exact hg b
    exact this hx

end

theorem term_of_primitive : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ, IsSD L S.Hm Λ → ∀ C, S.IsCls C → ∀ p ∈ C, S.sat Λ = S.Mof p.1 p.2 → ∃ d, S.IsTerm d Λ ∧ S.Fr d Λ = C ∧ S.BBzero d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ C hC p hp hs
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hs
  obtain ⟨hli, -, -, -, -, h0, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hon, hon', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hO : algebraMap F E S.th ∈ L.O :=
    (L.O_def _).2 (isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨S.th, hth⟩))
  obtain ⟨hf, hf', hd⟩ := linearIndependent_sum.1 hli
  have hf1 : LinearIndependent E S.f := hf
  have hf2 : LinearIndependent E S.f' := hf'
  have hd1 : Disjoint (Submodule.span E (Set.range S.f)) (Submodule.span E (Set.range S.f')) := hd
  have hi : LinearIndependent E fun b => n (S.f b) :=
    hf1.map' (n : S.V →ₗ[E] S.V) n.ker
  have hi' : LinearIndependent E fun b => n' (S.f' b) :=
    hf2.map' (n' : S.V →ₗ[E] S.V) n'.ker
  have hg : ∀ b, n (S.f b) ∈ Submodule.span E (Set.range S.f) := by
    obtain ⟨s, -, h⟩ := hon n hn
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg' : ∀ b, n' (S.f' b) ∈ Submodule.span E (Set.range S.f') := by
    obtain ⟨s, -, h⟩ := hon' n' hn'
    intro b
    rw [h b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA, m, hm, hme, hΛA⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) Λ hΛ n hn
    (trace_iff S Λ S.f S.f' _ _ hd1 hg hg' hi' le_sup_left hs)
  obtain ⟨A', hA', m', hm', hme', hΛA'⟩ := GlobalTheory.HL.FrameLift.lift L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) Λ hΛ n' hn'
    (trace_iff S Λ S.f' S.f _ _ hd1.symm hg' hg hi le_sup_right (hs.trans (Mof_swap S h0 hO _ _)))
  have hW : S.IsTermW (A, A', S.graphOf Λ) Λ m m' := by
    refine ⟨hA, hA', hm, hm', hΛA, hΛA', fun b => ?_, rfl⟩
    rw [hme, hme']
    have h1 := diff_mem S (fun b => n (S.f b)) (fun b => n' (S.f' b)) b
    rw [← hs] at h1
    exact ⟨_, h1.1, (th_smul S h0 _).symm⟩
  obtain ⟨-, hM, hFr, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S _ _ _ _ hW
  simp only [hme, hme'] at hM hFr
  exact ⟨_, ⟨(m, m'), hW⟩, hFr, hM.trans hs.symm⟩

end GlobalTheory.HL.PrimTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAll
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem natCast_isUnit_ae {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (N : ℕ) (hN : N ≠ 0) :
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  have hx : ((N : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {((N : 𝓞 F))} ≠ ⊥ := by simpa using hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation F (N : F) = 1 := by
    have : ((N : F)) = algebraMap (𝓞 F) F (N : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hmem
  have hι : (A.loc p).ιF (N : F) = (N : (A.loc p).Fp) := map_natCast _ _
  have h1 : (N : (A.loc p).Fp) ≤ᵥ 1 := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have h2 : (1 : (A.loc p).Fp) ≤ᵥ (N : (A.loc p).Fp) := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have hmem1 : (N : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff]; exact (Valuation.vle_one_iff (v := valuation _)).1 h1
  have hN0 : (N : (A.loc p).Fp) ≠ 0 := by
    haveI := (A.loc p).char0; exact Nat.cast_ne_zero.2 hN
  have hmem2 : (N : (A.loc p).Fp)⁻¹ ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, inv_le_one₀]
    · have := (Valuation.vle_iff_le (v := valuation _)).1 h2; rwa [map_one] at this
    · exact (Valuation.pos_iff _).2 hN0
  refine ⟨⟨⟨_, hmem1⟩, ⟨_, hmem2⟩, ?_, ?_⟩, rfl⟩
  · ext; simp [mul_inv_cancel₀ hN0]
  · ext; simp [inv_mul_cancel₀ hN0]

end GlobalTheory.HL.Glue
end

