module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemFlagUnipotentIffOrderedEichlerProduct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagUnipotentNormalFormRescaled
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NormalFormRescaled

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem eich_smul_base (c : E) (hc : L.cj c = c) (x u : Fin n → E) (s : E) (v : Fin n → E) :
    eich L Hm (c • x) u s v = eich L Hm x (c • u) (c ^ 2 * s) v := by
  simp only [eich, Eichler.hf_smul_r, Eichler.hf_smul_l, hc]
  module

theorem cj_alg (a : F) : L.cj (algebraMap F E a) = algebraMap F E a := L.cj.commutes a

omit [TopologicalSpace E] in
theorem alg_inv_mul (a : Fˣ) : algebraMap F E ((a⁻¹ : Fˣ) : F) * algebraMap F E (a : F) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

omit [TopologicalSpace E] in
theorem alg_mul_inv (a : Fˣ) : algebraMap F E (a : F) * algebraMap F E ((a⁻¹ : Fˣ) : F) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

end

end GlobalTheory.HL.NormalFormRescaled


open GlobalTheory.HL.NormalFormRescaled in
theorem GlobalTheory.HL.nof_normal_form_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hsel a X Y hX hY
  have hgg : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.gram]; simp [Fin.castSucc_ne_last]
    · rw [S.gram']; simp [Fin.castSucc_ne_last]
  have hgs : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (gs j) = if i = j then 1 else 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.dual]; simp [Fin.castSucc_inj]
    · rw [S.dual']; simp [Fin.castSucc_inj]
  have hss : ∀ i j : Fin r, hf L S.Hm (gs i) (gs j) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · exact S.iso i j
    · exact S.iso' i j
  have hg : ∀ i, g i.castSucc = algebraMap F E ((a i)⁻¹ : Fˣ) • X i := by
    intro i; rw [← hX i, smul_smul, alg_inv_mul, one_smul]
  have hY' : ∀ i, Y i = algebraMap F E ((a i)⁻¹ : Fˣ) • gs i := by
    intro i; rw [hY i, smul_smul, alg_inv_mul, one_smul]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun n => ?_⟩
  · simp only [Frames.h]
    rw [← hX i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, hgs]
    split_ifs with h
    · subst h; rw [mul_one, alg_mul_inv]
    · simp
  · simp only [Frames.h]
    rw [← hX i, ← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, hgg]; simp
  · simp only [Frames.h]
    rw [hY' i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, hss]; simp
  rw [_root_.GlobalTheory.FlagEich.main L r k S g gs hsel n]
  constructor
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E ((a i)⁻¹ : Fˣ) • u i,
      fun i => algebraMap F E ((a i)⁻¹ : Fˣ) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _)]
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E (a i : F) • u i,
      fun i => algebraMap F E (a i : F) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [hg j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _), smul_smul, ← mul_assoc, ← mul_pow,
        alg_inv_mul, one_pow, one_mul, one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplAct

open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (h : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) : x ∈ h • Λ ↔ h⁻¹ x ∈ Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : h⁻¹ (h • y) = y := h.symm_apply_apply y
    rwa [this]
  · intro hx
    exact ⟨_, hx, h.apply_symm_apply x⟩

theorem isSD_smul {h : S.GLV} (hh : h ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) :
    IsSD L S.Hm (h • Λ) := by
  refine ⟨⟨hΛ.1.1.map _, ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have h1 : h⁻¹ x ∈ Submodule.span E (Λ : Set S.V) := by rw [hΛ.1.2]; trivial
    have h2 := Submodule.mem_map_of_mem (f := h.toLinearMap) h1
    rw [Submodule.map_span] at h2
    have h3 : h.toLinearMap (h⁻¹ x) = x := h.apply_symm_apply x
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem_pointwise_smul y h Λ hy
  · rw [mem_smul, ← hΛ.2]
    have hi := (isomG L S.Hm).inv_mem hh
    constructor
    · intro H x hx
      have := H (h x) (Submodule.smul_mem_pointwise_smul x h Λ hx)
      rw [← hi] at this
      have h3 : h⁻¹ (h x) = x := h.symm_apply_apply x
      rwa [h3] at this
    · intro H x hx
      rw [← hi]
      exact H _ ((mem_smul S h Λ x).1 hx)

theorem spanTo_mono (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun _ hi => Nat.lt_succ_of_lt hi)

theorem mem_spanTo (g : Fin (r + 1) → S.V) (b : Fin (r + 1)) : g b ∈ S.spanTo g (r + 1) :=
  Submodule.subset_span ⟨b, b.2, rfl⟩

theorem spanTo_le_perp {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) :
    S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  rw [Frames.spanTo, image_lt, SetLike.mem_coe, mem_perp_span]
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro j; simp [S.gram, Fin.castSucc_ne_last]
  · intro j; simp [S.gram', Fin.castSucc_ne_last]

theorem nof_mem {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {n : S.GLV} (hn : n ∈ S.Nof g)
    {x : S.V} (hx : x ∈ S.spanTo g (r + 1)) : n x ∈ S.spanTo g (r + 1) := by
  have := spanTo_mono S g (hn.2.2 x (spanTo_le_perp S hg hx))
  simpa using Submodule.add_mem _ this hx

theorem perp_map {h : S.GLV} (hh : h ∈ isomG L S.Hm) {Y : Submodule E S.V} (hY : ∀ y ∈ Y, h y = y)
    {x : S.V} (hx : x ∈ perp L S.Hm Y) : h x ∈ perp L S.Hm Y := fun y hy => by
  rw [← hY y hy, hh x y]; exact hx y hy

theorem inv_fix {h : S.GLV} {x : S.V} (hx : h x = x) : h⁻¹ x = x := by
  conv_lhs => rw [← hx]
  exact h.symm_apply_apply x

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem inner_iff {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • S.stdLat g gs A, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  rw [(stdLat_spec L r k S g gs hg A hA).2.2 x]
  have hi := (S.Nof g).inv_mem hn
  constructor
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n y, Submodule.smul_mem_pointwise_smul y n _ hy, (hn.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hn.2.2 y h1) h2
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n⁻¹ y, (mem_smul S n _ y).1 hy, (hi.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hi.2.2 y h1) h2

theorem side {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) {h : S.GLV} (hh : h ∈ isomG L S.Hm)
    (hfix : ∀ x ∈ S.spanTo g (r + 1), h x = x) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ b, m (g b) = n (g b)) ∧
      h • n • S.stdLat g gs A = m • S.stdLat g gs (h • A) := by
  have hs := stdLat_spec L r k S g gs hg A hA
  have hi := (S.Nof g).inv_mem hn
  have hhi := (isomG L S.Hm).inv_mem hh
  have hfi : ∀ x ∈ S.spanTo g (r + 1), h⁻¹ x = x := fun x hx => inv_fix S (hfix x hx)
  have hsp : n • Submodule.span L.O (g '' {i | (i : ℕ) < r + 1}) =
      Submodule.span L.O (Set.range fun b => n (g b)) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [Submodule.smul_span, hs, Set.image_univ, Set.smul_set_range]
    rfl
  obtain ⟨B, hB, m, hm, hmn, hL⟩ := _root_.GlobalTheory.HL.FrameLift.lift L r k S g gs hg (h • n • S.stdLat g gs A)
    (isSD_smul S hh (isSD_smul S hn.1.1 hs.1)) n hn (fun x => by
      rw [← hsp, mem_smul S n, ← hs.2.1 _ le_rfl, mem_smul, mem_smul]
      constructor
      · rintro ⟨h1, h2⟩
        rw [hfi x h2] at h1
        exact ⟨h1, nof_mem S hg hi h2⟩
      · rintro ⟨h1, h2⟩
        have h3 := nof_mem S hg hn h2
        have h4 : n (n⁻¹ x) = x := n.apply_symm_apply x
        rw [h4] at h3
        exact ⟨by rwa [hfi x h3], h3⟩)
  have hBA : B = h • A := by
    ext x
    rw [inner_iff S hg hB hm, ← hL, mem_smul, inner_iff S hg hA hn]
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨h⁻¹ y, (mem_smul S h _ y).1 hy,
        perp_map S hhi (fun y hy => hfi y (spanTo_mono S g hy)) h1, ?_⟩
      rw [← map_sub, hfi _ (spanTo_mono S g h2)]; exact h2
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨h y, Submodule.smul_mem_pointwise_smul y h _ hy,
        perp_map S hh (fun y hy => hfix y (spanTo_mono S g hy)) h1, ?_⟩
      have h4 : h (h⁻¹ x) = x := h.apply_symm_apply x
      have h5 := hfix _ (spanTo_mono S g h2)
      rw [map_sub, h4] at h5
      rw [h5]; exact h2
  subst hBA
  exact ⟨hB, m, hm, hmn, hL⟩

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hermitianFrames_complementUnitary_fixes_ME {h : S.GLV} (hh : h ∈ S.H0) : ∀ x ∈ S.ME, h x = x := fun x hx =>
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 x hx))

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem graph_mem {h : S.GLV} (hh : h ∈ S.H0) {Λ : Submodule L.O S.V} {p : S.V × S.V}
    (hp : p ∈ S.graphOf Λ) : h • p ∈ S.graphOf (h • Λ) := by
  have hX : ∀ x ∈ S.X, h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_left (spanTo_mono S _ hx))
  have hX' : ∀ x ∈ S.X', h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_right (spanTo_mono S _ hx))
  obtain ⟨y', hy', y, hy, h1, h2, h3, h4, z, hz, h5⟩ := hp
  refine ⟨h y', Submodule.smul_mem_pointwise_smul y' h _ hy', h y,
    Submodule.smul_mem_pointwise_smul y h _ hy, perp_map S hh.1 hX' h1, perp_map S hh.1 hX h2, ?_, ?_,
    h z, Submodule.smul_mem_pointwise_smul z h _ hz, ?_⟩
  · change h y' - h p.1 ∈ _
    rw [← map_sub, hX' _ h3]; exact h3
  · change h y - h p.2 ∈ _
    rw [← map_sub, hX _ h4]; exact h4
  · rw [← map_sub, h5, map_smul]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem graph_smul {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) :
    h • S.graphOf Λ = S.graphOf (h • Λ) := by
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hp
    simpa using graph_mem S hh hp
  · intro hp
    simpa using graph_mem S (S.H0.inv_mem hh) hp

theorem comm {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : s * h = h * s := by
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hdis := (linearIndependent_sum.1 hli).2.2
  have hle : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ Submodule.span E (Set.range g) := fun g =>
    Submodule.span_mono (Set.image_subset_range _ _)
  have hW : ∀ w ∈ S.W0, s w = w := fun w hw => by
    have h1 := hs.1.2.2 w fun y hy => hw y (Submodule.mem_sup_left (spanTo_mono S _ hy))
    have h2 := hs.2.2.2 w fun y hy => hw y (Submodule.mem_sup_right (spanTo_mono S _ hy))
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hdis _ (hle _ h1) (hle _ h2))
  have hM : ∀ x ∈ S.ME, s x ∈ S.ME := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (nof_mem S (Or.inl ⟨rfl, rfl⟩) hs.1 ha)
      (nof_mem S (Or.inr ⟨rfl, rfl⟩) hs.2 hb)
  ext1 v
  have hv : v ∈ S.ME ⊔ S.W0 := by rw [hco.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  change s (h (a + b)) = h (s (a + b))
  rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hermitianFrames_complementUnitary_fixes_ME S hh a ha, hermitianFrames_complementUnitary_fixes_ME S hh _ (hM a ha), hW b hb,
    hW _ (perp_map S hh.1 (hermitianFrames_complementUnitary_fixes_ME S hh) hb)]

theorem termW {d : S.Datum} {Λ : Submodule L.O S.V} {n n' : S.GLV} (H : S.IsTermW d Λ n n')
    {h : S.GLV} (hh : h ∈ S.H0) :
    ∃ m m', S.IsTermW (h • d) (h • Λ) m m' ∧ (∀ b, m (S.f b) = n (S.f b)) ∧
      ∀ b, m' (S.f' b) = n' (S.f' b) := by
  obtain ⟨hA, hA', hn, hn', h1, h2, h3, h4⟩ := H
  obtain ⟨hB, m, hm, hmn, hL⟩ := side S (Or.inl ⟨rfl, rfl⟩) hA hn hh.1
    fun x hx => hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_left hx)
  obtain ⟨hB', m', hm', hmn', hL'⟩ := side S (Or.inr ⟨rfl, rfl⟩) hA' hn' hh.1
    fun x hx => hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_right hx)
  refine ⟨m, m', ⟨hB, hB', hm, hm', by rw [← h1] at hL; exact hL, by rw [← h2] at hL'; exact hL',
    fun b => ?_, ?_⟩, hmn, hmn'⟩
  · obtain ⟨z, hz, h5⟩ := h3 b
    refine ⟨h z, Submodule.smul_mem_pointwise_smul z h _ hz, ?_⟩
    rw [hmn, hmn', ← map_smul, ← h5, hermitianFrames_complementUnitary_fixes_ME S hh]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_right (nof_mem S (Or.inr ⟨rfl, rfl⟩) hn' (mem_spanTo S _ b)))
      (Submodule.mem_sup_left (nof_mem S (Or.inl ⟨rfl, rfl⟩) hn (mem_spanTo S _ b)))
  · rw [← graph_smul S hh, ← h4]; rfl

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.H0, S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ ∧ S.M (h • d) (h • Λ) = S.M d Λ ∧ S.sat (h • Λ) = S.sat Λ ∧ S.Fr (h • d) (h • Λ) = S.Fr d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ ⟨⟨n, n'⟩, H⟩ h hh
  obtain ⟨m, m', H', hm, hm'⟩ := termW S H hh
  obtain ⟨a1, a2, a3, -⟩ := _root_.GlobalTheory.HL.WitIndep.witness_independence L r k S _ _ _ _ H
  obtain ⟨b1, b2, b3, -⟩ := _root_.GlobalTheory.HL.WitIndep.witness_independence L r k S _ _ _ _ H'
  refine ⟨⟨(m, m'), H'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, b1]
    simp only [Frames.psi, Frames.psi', Frames.psiOf, Frames.coef, hm, hm']
  · unfold Frames.mu
    congr 1
    ext s
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hs => ?_
    rw [smul_smul, comm S hh hs, ← smul_smul, smul_left_cancel_iff]
  · rw [a2, b2]; simp only [hm, hm']
  · ext x
    simp only [Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine and_congr_left fun hx => ?_
    rw [mem_smul, inv_fix S (hermitianFrames_complementUnitary_fixes_ME S hh x hx)]
  · rw [a3, b3]; simp only [hm, hm']

end GlobalTheory.HL.ComplAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfIntegralAllQuadraticCompletions
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GlueInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem nonempty_place' : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem nontrivial_Ep (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) : Nontrivial (A.loc p).Ep :=
  Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := nonempty_place' (F := F)
  haveI := nontrivial_Ep A p
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem sig_ne_id (A : Places F E sig) : ¬ ∀ y, sig y = y := by
  intro h
  obtain ⟨p⟩ := nonempty_place' (F := F)
  have hcj : (A.L p).cj.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range (A.loc p).span fun y => by
      simp [A.L_cj, (A.loc p).cj_ιE, h]
  have hall : ∀ z : (A.loc p).Ep, ∃ c : (A.loc p).Fp, c • (1 : (A.loc p).Ep) = z := fun z => by
    obtain ⟨a, ha⟩ := ((A.L p).cj_fix z).1 (by simpa using LinearMap.congr_fun hcj z)
    exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  have := finrank_le_one (1 : (A.loc p).Ep) hall
  rw [(A.loc p).rank] at this
  norm_num at this

theorem fix_mem (A : Places F E sig) (s : E) (hs : sig s = s) : ∃ t : F, algebraMap F E t = s := by
  by_contra hno
  push_neg at hno
  apply sig_ne_id A
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
      have hab' : algebraMap F E a + algebraMap F E b * s = 0 := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab; exact hab
      apply hno (-a / b)
      rw [map_div₀, map_neg, div_eq_iff hb']
      linear_combination (-1 : E) * hab'
  have hspan : Submodule.span F (Set.range ![(1 : E), s]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, A.quad]
    simp
  have hid : sig.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range hspan fun i => by
      fin_cases i <;> simp [hs]
  exact fun y => LinearMap.congr_fun hid y

theorem int_of_loc (A : Places F E sig) (t : F)
    (h : ∀ p, (A.loc p).ιE (algebraMap F E t) ∈ (A.L p).O) : t ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro p
  haveI := nontrivial_Ep A p
  have h1 := h p
  rw [(A.loc p).compat, (A.L p).O_def] at h1
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] ((A.loc p).ιF t) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h1
  have h3 := (Valuation.integer.integers (valuation (A.loc p).Fp)).mem_of_integral h2
  have h4 : (A.loc p).ιF t ≤ᵥ (A.loc p).ιF 1 := by
    rw [map_one]
    exact (Valuation.Compatible.vle_iff_le (v := valuation (A.loc p).Fp) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 h3)
  simpa using ((A.loc p).val t 1).1 h4

theorem sig_mem (A : Places F E sig) (y : E) (p : HeightOneSpectrum (𝓞 F))
    (hy : (A.loc p).ιE y ∈ (A.L p).O) : (A.loc p).ιE (sig y) ∈ (A.L p).O := by
  rw [← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).O_def]
  exact (((A.L p).O_def _).1 hy).map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

theorem isIntegral_of_quadratic (y a b : E) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (h : y ^ 2 - a * y + b = 0) : IsIntegral ℤ y := by
  have hR : IsIntegral (integralClosure ℤ E) y := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, ha⟩ : integralClosure ℤ E) * Polynomial.X +
      Polynomial.C (⟨b, hb⟩ : integralClosure ℤ E), by monicity!, ?_⟩
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul] using h
  exact isIntegral_trans y hR

end GlobalTheory.HL.GlueInt


open GlobalTheory.HL.GlueInt in
theorem GlobalTheory.HL.isIntegral_of_forall_mem_O : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) →
    IsIntegral ℤ y := by
  intro F E _ _ _ _ _ sig A y hy
  obtain ⟨a, ha⟩ := fix_mem A (y + sig y) (by rw [map_add (f := _), sig_sig A, add_comm])
  obtain ⟨b, hb⟩ := fix_mem A (y * sig y) (by rw [map_mul, sig_sig A, mul_comm])
  obtain ⟨a0, rfl⟩ := int_of_loc A a fun p => by
    rw [ha, map_add (f := _)]; exact (A.L p).O.add_mem (hy p) (sig_mem A y p (hy p))
  obtain ⟨b0, rfl⟩ := int_of_loc A b fun p => by
    rw [hb, map_mul]; exact (A.L p).O.mul_mem (hy p) (sig_mem A y p (hy p))
  refine isIntegral_of_quadratic y _ _ ((RingOfIntegers.isIntegral_coe a0).map (algebraMap F E).toIntAlgHom)
    ((RingOfIntegers.isIntegral_coe b0).map (algebraMap F E).toIntAlgHom) ?_
  change y ^ 2 - algebraMap F E (algebraMap (𝓞 F) F a0) * y + algebraMap F E (algebraMap (𝓞 F) F b0) = 0
  rw [ha, hb]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m i : ℕ), 1 ≤ i → (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i ∧ (∀ A ∈ congK L ϖ m i, IsIntM L A ∧ IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ A⁻¹ ∈ congK L ϖ m i ∧ (∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i) ∧ ∀ i' ≥ i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' ∧ B ∈ congK L ϖ m i) ∧ ∀ Γ : Matrix (Fin m) (Fin m) E, IsHerm L Γ → IsUnit Γ.det → IsCO (hermLat L m) (horb L ϖ Γ i) ∧ 0 < cont (hermLat L m) (horb L ϖ Γ i) := by
  first | exact @GlobalTheory.CongGrp.congK_group | exact GlobalTheory.CongGrp.congK_group | (intros; apply GlobalTheory.CongGrp.congK_group <;> assumption)
end

