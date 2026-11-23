module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadratic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContCxOfDegreewise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CochainLim

universe v u w w'
variable {C : Type u} [Category.{v} C] [Preadditive C]

def pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) : Cochain A L n :=
  (Cochain.ofHom f).comp z (zero_add n)

theorem pb_v {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (p q : ℤ)
    (h : p + n = q) : (pb f z).v p q h = f.f p ≫ z.v p q h := by
  simp [pb]

theorem pb_pb {A B D L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (g : B ⟶ D) (z : Cochain D L n) :
    pb f (pb g z) = pb (f ≫ g) z := by
  ext p q h; simp [pb_v]

theorem pb_add {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z + z') = pb f z + pb f z' := by simp [pb]

theorem pb_sub {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z - z') = pb f z - pb f z' := by simp [pb]

theorem pb_zero {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) :
    pb f (0 : Cochain B L n) = 0 := by simp [pb]

theorem δ_pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (m : ℤ) :
    δ n m (pb f z) = pb f (δ n m z) := by simp [pb]

section Rel
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

def Q (n m a : ℤ) : Prop :=
  ∀ (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n), δ m (m + 1) w = 0 →
    δ n m z = pb (c.π.app i) w → (∀ p q (h : p + m = q), a < p → w.v p q h = 0) →
    (∀ p q (h : p + n = q), a < p → z.v p q h = 0) →
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y

theorem Q_base (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p)) (n m a : ℤ) (ham : a + m < 0) (han : a + n < 0) :
    Q c L n m a := by
  intro i w z hw hz hw0 hz0
  have w0 : w = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hw0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  have z0 : z = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hz0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  exact ⟨i, 𝟙 i, 0, 0, by simp [w0, pb_zero], by simp [z0, pb_zero]⟩

end Rel

section Step
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem Q_of_Q_sub_one
    (hA : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s')
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (p : ℤ) (ih : Q c L n m (p - 1)) : Q c L n m p := by
  intro i w z hw hz hw0 hz0
  obtain ⟨s, hs⟩ : ∃ s, p + m = s := ⟨_, rfl⟩
  have hwc : w.v p s hs ≫ L.d s (s + 1) = 0 := by
    have := Cochain.congr_v hw p (s + 1) (by omega)
    rw [δ_v m (m + 1) rfl w p (s + 1) (by omega) s (p + 1) (by omega) rfl, Cochain.zero_v,
      hw0 (p + 1) (s + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hzw : (c.π.app i).f p ≫ w.v p s hs = z.v p (s - 1) (by omega) ≫ L.d (s - 1) s := by
    have := Cochain.congr_v hz p s hs
    rw [δ_v n m hnm z p s hs (s - 1) (p + 1) rfl rfl,
      hz0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v] at this
    exact this.symm
  obtain ⟨k, f, y', hy'⟩ := hB p s i (w.v p s hs) hwc ⟨_, hzw⟩
  have hδσ := Cochain.δ_single y' n m hnm (p - 1) s (by omega) (by omega)
  set σ : Cochain (K.obj k) L n := Cochain.single y' n with hσ
  set w' := pb (K.map f) w - δ n m σ with hw'def
  set z' := z - pb (A := c.pt) (c.π.app k) σ with hz'def
  have hw' : δ m (m + 1) w' = 0 := by
    simp only [hw'def, δ_sub, δ_pb, hw, pb_zero, δ_δ, sub_zero]
  have hz' : δ n m z' = pb (c.π.app k) w' := by
    simp only [hz'def, hw'def, δ_sub, δ_pb, hz, pb_sub, pb_pb, c.w f]
  have hw'0 : ∀ p'' q (h : p'' + m = q), p - 1 < p'' → w'.v p'' q h = 0 := by
    intro p'' q h hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s := by omega
      simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v, hy',
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero, sub_self]
    · simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hw0 p'' q h (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  have hz'0 : ∀ p'' q (h : p'' + n = q), p < p'' → z'.v p'' q h = 0 := by
    intro p'' q h hp''
    simp only [hz'def, hσ, Cochain.sub_v, pb_v, hz0 p'' q h hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p by omega), comp_zero, sub_self]
  have hz'c : z'.v p (s - 1) (by omega) ≫ L.d (s - 1) s = 0 := by
    have := Cochain.congr_v hz' p s hs
    rw [δ_v n m hnm z' p s hs (s - 1) (p + 1) rfl rfl,
      hz'0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v,
      hw'0 p s hs (by omega), comp_zero] at this
    exact this
  obtain ⟨j, u2, y2, hu2c, hu2⟩ := hA p s (s - 1) (by omega) _ hz'c
  let l := IsCofiltered.min j k
  let g : l ⟶ j := IsCofiltered.minToLeft j k
  let h : l ⟶ k := IsCofiltered.minToRight j k
  have hδv := Cochain.δ_single ((K.map g).f p ≫ u2) n m hnm (p - 1) s (by omega) (by omega)
  rw [Category.assoc, hu2c, comp_zero, Cochain.single_zero, zero_add] at hδv
  set v : Cochain (K.obj l) L n := Cochain.single ((K.map g).f p ≫ u2) n with hv
  have hδρ := Cochain.δ_single y2 (n - 1) n (by omega) (p - 1) (s - 1) (by omega) (by omega)
  set ρ : Cochain c.pt L (n - 1) := Cochain.single y2 (n - 1) with hρ
  set w'' := pb (K.map h) w' - δ n m v with hw''def
  set z'' := z' - pb (A := c.pt) (c.π.app l) v + δ (n - 1) n ρ with hz''def
  have hw'' : δ m (m + 1) w'' = 0 := by
    simp only [hw''def, δ_sub, δ_pb, hw', pb_zero, δ_δ, sub_zero]
  have hz'' : δ n m z'' = pb (c.π.app l) w'' := by
    simp only [hz''def, hw''def, δ_add, δ_sub, δ_pb, hz', δ_δ, add_zero, pb_sub, pb_pb, c.w h]
  have hw''0 : ∀ p'' q (hh : p'' + m = q), p - 1 < p'' → w''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    simp only [hw''def, hδv, Cochain.sub_v, Cochain.units_smul_v, pb_v, hw'0 p'' q hh hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, comp_zero, sub_self]
  have hz''0 : ∀ p'' q (hh : p'' + n = q), p - 1 < p'' → z''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s - 1 := by omega
      simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, c.w g, hu2]
      abel
    · simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hz'0 p'' q hh (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  obtain ⟨k', f', b'', y'', hb'', hby''⟩ := ih l w'' z'' hw'' hz'' hw''0 hz''0
  refine ⟨k', f' ≫ h ≫ f, b'' + pb (K.map f') v + pb (K.map (f' ≫ h)) σ, y'' + ρ, ?_, ?_⟩
  · simp only [δ_add, δ_pb, hb'', hw''def, hw'def, pb_sub, pb_pb, Functor.map_comp, Category.assoc]
    abel
  · simp only [pb_add, pb_pb, c.w, hby'', hz''def, hz'def, δ_add]
    abel

end Step

section Main
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem relative
    (hK : ∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) (hc : ∀ p : ℤ, 0 < p → IsZero (c.pt.X p))
    (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
    (hA : ∀ (p s : ℤ) (t : c.pt.X p ⟶ L.X s), t ≫ L.d s (s + 1) = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)),
        u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s)
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n)
    (hw : δ m (m + 1) w = 0) (hz : δ n m z = pb (c.π.app i) w) :
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y := by
  have hA' : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s' := by
    intro p s s' h
    subst h
    exact hA p s'
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = -|m| - 2 := ⟨_, rfl⟩
  have hall : ∀ k : ℕ, Q c L n m (a + k) := by
    intro k
    induction k with
    | zero =>
      simpa using Q_base c L hL n m a (by linarith [le_abs_self m]) (by linarith [le_abs_self m])
    | succ k ih =>
      have := Q_of_Q_sub_one c L hA' hB n m hnm (a + (k + 1 : ℕ)) (by
        rw [show a + ((k + 1 : ℕ) : ℤ) - 1 = a + k by push_cast; ring]; exact ih)
      exact this
  have h0 := hall (-a).toNat
  rw [show a + ((-a).toNat : ℤ) = 0 by
    have : 0 ≤ -a := by rw [ha]; linarith [abs_nonneg m]
    omega] at h0
  exact h0 i w z hw hz (fun p q h hp => (hK i p hp).eq_of_src _ _) (fun p q h hp => (hc p hp).eq_of_src _ _)

end Main

end GlobalTheory.CochainLim


open GlobalTheory.CochainLim in
theorem GlobalTheory.EtC.cont_cx_of_degreewise : ∀ (R : Type) [CommRing R] (I : Type) [SmallCategory I] [IsCofiltered I] (K : I ⥤ Cx R) (c : Cone K) (L : Cx R), (∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) → (∀ p : ℤ, 0 < p → IsZero (c.pt.X p)) → (∀ p : ℤ, p < 0 → IsZero (L.X p)) → (∀ p s : ℤ, (∀ t : c.pt.X p ⟶ L.X s, t ≫ L.d s (s + 1) = 0 → ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)), u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s) ∧ ∀ (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 → (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) → ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s) → ∀ n : ℤ, (∀ x : CohomologyClass c.pt L n, ∃ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = x) ∧ ∀ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = 0 → ∃ (k : I) (f : k ⟶ i), cpre (Cocycle.ofHom (K.map f)) L n n (zero_add n) y = 0 := by
  intro R _ I _ _ K c L hK hc hL hAB n
  have rel := relative c L hK hc hL (fun p s => (hAB p s).1) (fun p s => (hAB p s).2)
  constructor
  · intro x
    obtain ⟨ζ, rfl⟩ := x.mk_surjective
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    obtain ⟨k, f, b, y, hb, hby⟩ := rel n (n + 1) rfl i 0 ζ.1 (by simp)
      (by rw [Cocycle.δ_eq_zero, pb_zero])
    rw [pb_zero] at hb
    refine ⟨k, CohomologyClass.mk (Cocycle.mk b (n + 1) rfl hb), ?_⟩
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨y, ?_⟩
    rw [Cocycle.coe_sub]
    change _ = pb (A := c.pt) (c.π.app k) b - ζ.1
    rw [hby]
    abel
  · intro i y hy
    obtain ⟨β, rfl⟩ := y.mk_surjective
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
    obtain ⟨γ, hγ⟩ := hy
    obtain ⟨k, f, b, y, hb, -⟩ := rel (n - 1) n (by omega) i β.1 γ (Cocycle.δ_eq_zero _ _) hγ
    refine ⟨k, f, ?_⟩
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨b, hb⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionIntegral
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

open scoped Pointwise in
theorem nhds_one_slice_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

  have hcl : IsClosed (Function.support Φ) := by
    have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
  have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [tsupport, hcl.closure_eq] at hY
    by_contra h; exact hY (hrk Y h)
  set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
    fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
  have hfc : ContinuousOn f (tsupport Φ) := by
    have hs' := hs.mono hS
    refine ContinuousOn.prodMk hs' ?_
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
      ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
  have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
  set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
    {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
  have hno : IsOpen n := by
    have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.2.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    exact (h1.prodMk h2) {q | q.1 = q.2}
  have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
    rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [hn]
  obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

  have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d → Φ (h.val * Z) ≠ 0 →
      (h, Z) ∈ f '' tsupport Φ := by
    intro h Z hZ hne
    have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
    have hr := hS hY
    have e : (s (h.val * Z))⁻¹ * h = 1 := by
      apply huniq Z _ hZ
      have := hsl _ hr
      simpa [Units.val_mul, Matrix.mul_assoc] using this
    have e' : s (h.val * Z) = h := by
      have := congrArg (fun t => s (h.val * Z) * t) e
      simpa [mul_assoc] using this.symm
    refine ⟨h.val * Z, hY, ?_⟩
    simp only [hf, e', Prod.mk.injEq, true_and]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
  · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
  rintro x ⟨hxv, hxv'⟩ g Z hZ
  by_cases h0 : Φ (g.val * Z) ≠ 0
  · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
  by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
  · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
    have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
    simp only [hn, Set.mem_ofPred_eq] at this
    rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    rw [this]
  push Not at h0 h0'
  rw [h0, h0']

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSliceSectionMeasure
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem exists_isCompact_of_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) := by
    exact (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hts : tsupport Φ = Function.support Φ := hclosed.closure_eq
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [hts] at hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hr : (g.val * Z).rank = a := hsub hY
  have h1 : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice (k := k) a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ hr
  have h2 := huniq Z _ hZ h1
  have : g = s (g.val * Z) := by
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  exact ⟨g.val * Z, hY, this.symm⟩

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

def defect (Q q : ℕ) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  (redMap Q q 1).app U 0 (kumT Q U v) - kumT q U (v ^ (Q / q))

def defectSec (Q q : ℕ) (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  pick fun s => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
    Sec.res g s = defect Q q V v

def corrFam (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 1, s, h, U, x => Sec.map ((res _ (tw q 1)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (defectSec Q q U (lineUnit L x))
  | _, _, _, _, _ => 0

theorem corrFam_zero (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E 0 U) : corrFam Q q L 0 s h U x = 0 := rfl

theorem corrFam_add_two (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : corrFam Q q L (p + 2) s h U x = 0 := rfl

theorem corrFam_one (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : corrFam Q q L 1 0 h U x = defectSec Q q U (lineUnit L x) := by
  simp [corrFam, Sec.map]

end GlobalTheory.EtC.RedChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingBound
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isEtaleAt_closure_of_disjoint : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    ∀ (Q : Ideal (GlobalTheory.KeyOriginNoeth.closure A R D)) [Q.IsPrime],
      (∀ a : A, a ≠ 0 → algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a) ∉ Q) →
      Algebra.IsEtaleAt R Q := by
  intro A R D _ _ _ _ _ _ _ _
  letI := closureAlg A R D
  intro Q _ hQ
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let SR : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let SC : Submonoid (closure A R D) := Algebra.algebraMapSubmonoid (closure A R D) SR
  have hCD : ∀ r : R, algebraMap (closure A R D) D (algebraMap R (closure A R D) r) = algebraMap R D r :=
    fun _ => rfl
  haveI : IsScalarTower R (closure A R D) D := IsScalarTower.of_algebraMap_eq (fun r => (hCD r).symm)
  have hunit : ∀ a : A, a ∈ nonZeroDivisors A → IsUnit (algebraMap R D (algebraMap A R a)) := by
    intro a ha
    have h1 : IsUnit (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) (algebraMap A R a)) :=
      IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R) (⟨algebraMap A R a, a, ha, rfl⟩ : SR)
    rw [IsScalarTower.algebraMap_apply R (GlobalTheory.LocAcyc.GenFib A R) D]
    exact h1.map _
  haveI hloc : IsLocalization SC D := by
    refine (isLocalization_iff SC D).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
      exact hCD _ ▸ hunit a ha
    · intro d
      have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
      obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization SR
        (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
      obtain ⟨a, ha, rfl⟩ := hm
      refine ⟨(⟨_, hmi⟩, ⟨algebraMap R (closure A R D) (algebraMap A R a), _, ⟨a, ha, rfl⟩, rfl⟩), ?_⟩
      show d * algebraMap (closure A R D) D (algebraMap R (closure A R D) (algebraMap A R a)) = _
      rw [hCD, mul_comm, ← Algebra.smul_def]
      rfl
    · intro x y h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hle : SC ≤ Q.primeCompl := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hQ a (nonZeroDivisors.ne_zero ha)
  letI : Algebra D (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsScalarTower (closure A R D) D (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl) (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q) SC Q.primeCompl hle
  haveI : Algebra.FormallyEtale D (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid D Q.primeCompl)
  haveI : Algebra.FormallyEtale R (GlobalTheory.LocAcyc.GenFib A R) := Algebra.FormallyEtale.of_isLocalization SR
  haveI : Algebra.FormallyEtale R D := Algebra.FormallyEtale.comp R (GlobalTheory.LocAcyc.GenFib A R) D
  haveI : IsScalarTower R D (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply R (closure A R D) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply (closure A R D) D (Localization.AtPrime Q), hCD])
  exact Algebra.FormallyEtale.comp R D (Localization.AtPrime Q)

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenNormClosedBallQuadraticStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by
  first | exact @GlobalTheory.NormBall.exists_normBall | exact GlobalTheory.NormBall.exists_normBall | (intros; apply GlobalTheory.NormBall.exists_normBall <;> assumption)
end

