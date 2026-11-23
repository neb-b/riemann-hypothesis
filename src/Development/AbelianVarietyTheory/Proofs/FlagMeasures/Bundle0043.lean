module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalFrameStabilizerActsUnitriangular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.StTri

theorem descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]

theorem hf_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem loc_step {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2

theorem frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel

theorem stab_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩

end GlobalTheory.HL.StTri
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (n : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ n • Λ ↔ ∃ y ∈ Λ, n y = x :=
  Submodule.mem_smul_pointwise_iff_exists x n Λ

theorem smul_eq_map (n : S.GLV) (Λ : Submodule L.O S.V) :
    n • Λ = Λ.map (n.toLinearMap.restrictScalars L.O) := by
  ext x
  rw [mem_smul, Submodule.mem_map]
  rfl

theorem isSD_smul {n : S.GLV} (hn : n ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (n • Λ) := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hn' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hn
  refine ⟨⟨by rw [smul_eq_map]; exact hfg.map _, ?_⟩, fun y => ?_⟩
  · have : ((n • Λ : Submodule L.O S.V) : Set S.V) = n.toLinearMap '' (Λ : Set S.V) := by
      rw [smul_eq_map]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨y, rfl⟩ := n.surjective y
    constructor
    · intro h
      refine (mem_smul S n Λ _).2 ⟨y, (hd y).1 fun x hx => ?_, rfl⟩
      rw [← hn']
      exact h _ ((mem_smul S n Λ _).2 ⟨x, hx, rfl⟩)
    · intro h x hx
      obtain ⟨y', hy', e⟩ := (mem_smul S n Λ _).1 h
      obtain ⟨x', hx', rfl⟩ := (mem_smul S n Λ _).1 hx
      rw [← e, hn']
      exact (hd y').2 hy' x' hx'

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem self_mem (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j := Submodule.subset_span ⟨i, h, rfl⟩

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  rw [Frames.spanTo, hs, Set.image_univ]

section
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg

theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) : n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨-, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine h3.2 _ ?_
    rw [Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
    exact hg _
  · exact (Subgroup.mem_iInf.1 h2 i).2 _ (self_mem S g (by simp))

theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {x : S.V} (hx : x ∈ S.spanTo g j) :
    n x ∈ S.spanTo g j := by
  have : S.spanTo g j ≤ (S.spanTo g j).comap n.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (S.spanTo g j).add_mem (spanTo_mono S g (le_of_lt hi) (sub_mem hg hn i))
      (self_mem S g hi)
    rw [sub_add_cancel] at h1
    exact h1
  exact this hx

theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (x : S.V) :
    n x ∈ S.spanTo g j ↔ x ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem hg hn j⟩
  have := map_mem hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n x) = x := n.symm_apply_apply x
  rwa [e] at this

theorem trace_smul {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V} {j : ℕ}
    (h : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) (x : S.V) :
    (x ∈ n • Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) := by
  have e : Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) =
      n • Submodule.span L.O (g '' {i | (i : ℕ) < j}) := by
    rw [smul_eq_map, Submodule.map_span, Set.image_image]; rfl
  rw [e, mem_smul, mem_smul]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    exact ⟨y, (h y).1 ⟨hy, (map_mem_iff hg hn j y).1 h2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, ((h y).2 hy).1, rfl⟩, map_mem hg hn j ((h y).2 hy).2⟩

end

theorem inner_smul {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (x : S.V) :
    (∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) ↔
      ∃ y ∈ n • Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, (mem_smul S n Λ _).2 ⟨y, hy, rfl⟩, (h1 y).2 hp, ?_⟩
    have := (S.spanTo g r).add_mem (h2 y hp) hx
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨_, hy, hp, hx⟩
    obtain ⟨y, hy0, rfl⟩ := (mem_smul S n Λ _).1 hy
    refine ⟨y, hy0, (h1 y).1 hp, ?_⟩
    have := (S.spanTo g r).sub_mem hx (h2 y ((h1 y).1 hp))
    rwa [sub_sub_sub_cancel_left] at this

theorem term_basic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hW : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dite_eq_left hT]
    exact hT.choose_spec
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  have det : ∀ d : S.Datum, S.IsTerm d Λ →
      (∀ x, x ∈ d.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f r) ∧ y - x ∈ S.spanTo S.f r) ∧
      (∀ x, x ∈ d.2.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f' r) ∧ y - x ∈ S.spanTo S.f' r) ∧
      d.2.2 = S.graphOf Λ := by
    rintro d ⟨p, hA, hA', hn, hn', e, e', -, hgr⟩
    refine ⟨fun x => ?_, fun x => ?_, hgr⟩
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 x, inner_smul S hn, ← e]
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 x, inner_smul S hn', ← e']
  obtain ⟨hA, hA', hn, hn', e, e', hth', hgr⟩ := id hW
  obtain ⟨s1, s2, -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨-, s2', -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := isSD_smul S hn.1.1 s1
    rwa [← e] at this
  have t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔
      x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg hn (s2 j hj) x
    rwa [← e] at this
  have t' : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔
      x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg' hn' (s2' j hj) x
    rwa [← e'] at this
  have m : ∀ b, S.fr d Λ b ∈ Λ ∧ S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    (t _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  have m' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (t' _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  refine ⟨hSD, hW, ?_, t, t', ?_, ⟨⟨_, hn, _, hn', rfl⟩, ?_⟩, fun d' hd' => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(m b).1, Submodule.mem_sup_left (m b).2⟩
    · refine ⟨?_, S.ME.smul_mem _ (S.ME.sub_mem (Submodule.mem_sup_right (m' b).2)
        (Submodule.mem_sup_left (m b).2))⟩
      obtain ⟨y, hy, e2⟩ := hth' b
      have e3 : S.fr' d Λ b - S.fr d Λ b = algebraMap F E S.th • y := e2
      simp only [e3, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      exact hy
  · obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
    refine LinearIndependent.sum_type (l1.map' (S.wit d Λ).1.toLinearMap (LinearEquiv.ker _))
      (l2.map' (S.wit d Λ).2.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m b).2
      rw [spanTo_top] at this
      exact this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m' b).2
      rw [spanTo_top] at this
      exact this
  · rintro p ⟨A, A', hi, hi', -, -, -, h1, h2⟩ a b
    refine (hSD.2 _).2 ?_ _ ?_
    · rw [h1]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi i a⟩ : L.O) (m i).1
    · rw [h2]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi' i b⟩ : L.O) (m' i).1
  · obtain ⟨a1, a2, a3⟩ := det d hT
    obtain ⟨b1, b2, b3⟩ := det d' hd'
    exact Prod.ext (Submodule.ext fun x => (b1 x).trans (a1 x).symm)
      (Prod.ext (Submodule.ext fun x => (b2 x).trans (a2 x).symm) (b3.trans a3.symm))

end GlobalTheory.HL.TermBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitia
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.LatComm

theorem finite_between {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R)
    [Finite (R ⧸ Ideal.span {c})] (Λ : Submodule R V) (hΛ : Λ.FG) :
    {M : Submodule R V | M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M}.Finite := by
  have hfg : (⊤ : Submodule R Λ).FG := (Submodule.fg_top Λ).2 hΛ
  have hf : Finite (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ)) :=
    Submodule.finite_quotient_smul _ hfg
  have hs : Finite (Submodule R (Λ ⧸ (Ideal.span {c}) • (⊤ : Submodule R Λ))) :=
    Finite.of_injective _ SetLike.coe_injective
  have key : ∀ M : Submodule R V, (M ≤ Λ ∧ ∀ v ∈ Λ, c • v ∈ M) →
      (((M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).comap
        ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ).map Λ.subtype = M := by
    intro M hM
    have h1 : (Ideal.span {c}) • (⊤ : Submodule R Λ) ≤ M.comap Λ.subtype := by
      rw [Submodule.smul_le]
      intro r hr v _
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact Submodule.smul_mem _ _ (hM.2 v v.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 h1, Submodule.map_comap_subtype,
      inf_eq_right.2 hM.1]
  refine Set.Finite.of_finite_image (f := fun M : Submodule R V =>
    (M.comap Λ.subtype).map ((Ideal.span {c}) • (⊤ : Submodule R Λ)).mkQ) (Set.toFinite _) ?_
  intro M hM N hN h
  rw [← key M hM, ← key N hN]
  simp only at h
  rw [h]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_smul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ j : ℕ, p ^ j • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMemOrder.main
  | exact _root_.GlobalTheory.PowMulMemOrder.main
  | (apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMemOrder.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMemOrder.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMemOrder.main ..)

theorem exists_pow_smul_le (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (p : L.O)
    (hp : (p : E) = algebraMap F E (ϖ : F)) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : Λ'.FG) :
    ∃ j : ℕ, ∀ v ∈ Λ', p ^ j • v ∈ Λ := by
  obtain ⟨s, rfl⟩ := hΛ'
  choose f hf using exists_pow_smul_mem L hϖ p hp hΛ
  refine ⟨s.sup f, fun v hv => ?_⟩
  have : Submodule.span L.O (s : Set (Fin n → E)) ≤
      Λ.comap (LinearMap.lsmul L.O (Fin n → E) (p ^ s.sup f)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hx)
    show p ^ s.sup f • x ∈ Λ
    rw [hk, pow_add, mul_smul]
    exact Λ.smul_mem _ (hf x)
  exact this hv

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Λ Λ' : Submodule L.O (Fin n → E)), IsLat L Λ → IsLat L Λ' → ∀ H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (H ⊓ stabL L Λ').relIndex (H ⊓ stabL L Λ) ≠ 0 ∧ ∀ g : ((Fin n → E) ≃ₗ[E] (Fin n → E)), IsLat L (g • Λ) ∧ stabL L (g • Λ) = MulAut.conj g • stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n Λ Λ' hΛ hΛ' H
  refine ⟨?_, fun g => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
    let p : L.O := ⟨algebraMap F E (ϖ : F), (hO _).2 ϖ.2⟩
    have hp : (p : E) = algebraMap F E (ϖ : F) := rfl
    obtain ⟨a, ha⟩ := exists_pow_smul_le L hϖ p hp hΛ hΛ'.1
    obtain ⟨b, hb⟩ := exists_pow_smul_le L hϖ p hp hΛ' hΛ.1
    have hfin : Finite (L.O ⧸ Ideal.span {p ^ (a + b)}) := by
      have h1 := hcard (a + b)
      have h2 : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ (a + b))} = {p ^ (a + b)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff,
          SubmonoidClass.coe_pow, hp, map_pow]
      rw [h2] at h1
      apply Nat.finite_of_card_ne_zero
      rw [h1]
      exact pow_ne_zero _ (by omega)
    have hF := finite_between (p ^ (a + b)) Λ hΛ.1
    have hu : IsUnit ((p ^ a : L.O) : E) := by
      rw [SubmonoidClass.coe_pow, hp]
      exact ((IsUnit.mk0 _ (fun h => hϖ.ne_zero (Subtype.ext h))).map (algebraMap F E)).pow a
    have hinj : Function.Injective (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) := by
      intro x y h
      exact hu.smul_left_cancel.1 h
    have hcomm : ∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (r : L.O) (v : Fin n → E),
        g • (r • v) = r • (g • v) := fun g r v => map_smul g (r : E) v
    have heq : (H ⊓ stabL L Λ').subgroupOf (H ⊓ stabL L Λ) =
        MulAction.stabilizer (H ⊓ stabL L Λ :) Λ' := by
      ext g
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
    rw [Subgroup.relIndex, heq, MulAction.index_stabilizer]
    refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ') ?_
    refine Set.Finite.of_finite_image
      (f := fun M => Submodule.map (LinearMap.lsmul L.O (Fin n → E) (p ^ a)) M) (hF.subset ?_)
      (Submodule.map_injective_of_injective hinj).injOn
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hg : g.1 • Λ = Λ := g.2.2
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w g.1 Λ').1 hw
      show p ^ a • (g.1 • x) ∈ Λ
      rw [← hcomm]
      exact hg.le (Submodule.smul_mem_pointwise_smul _ _ _ (ha x hx))
    · rw [← hg] at hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g.1 Λ).1 hv
      refine ⟨g.1 • (p ^ b • x), Submodule.smul_mem_pointwise_smul _ g.1 _ (hb x hx), ?_⟩
      rw [LinearMap.lsmul_apply, hcomm, pow_add, mul_smul]
  · exact hΛ.1.map _
  · rw [eq_top_iff]
    intro v _
    have hv : g.symm v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : (Fin n → E) →ₗ[E] (Fin n → E)) hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_pointwise_smul _ g _ hx
  · exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Λ

end GlobalTheory.LatComm
end

