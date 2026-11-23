module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocOne
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem locOne_nak {L : Type} [Field L] [Algebra ℂ L] (B O : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (hBO : B ≤ O) (ev : O →ₐ[ℂ] ℂ) (hunit : ∀ u : O, ev u ≠ 0 → IsUnit u)
    (hden : ∀ v : O, ∃ b : B, ev ⟨b, hBO b.2⟩ ≠ 0 ∧ (b : L) * v ∈ B)
    {d : ℕ} (t : Fin d → O) (ht : ∀ l, ev (t l) = 0)
    (hmax : ∀ v : O, ev v = 0 → ∃ a : Fin d → O, v = ∑ l, a l * t l) (v : O) :
    D ℂ L (v : L) ∈ Submodule.span O (Set.range fun l => D ℂ L (t l : L)) := by
  classical
  set I : Ideal O := RingHom.ker ev with hI
  set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN
  set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM
  have hvM : D ℂ L (v : L) ∈ M := Submodule.subset_span ⟨v, rfl⟩
  suffices hMN : M ≤ N from hMN hvM
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ B).out
    set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG
    have hB : ∀ b : B, D ℂ L (b : L) ∈ G := by
      intro b
      have hb : b ∈ Algebra.adjoin ℂ (s : Set B) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | algebraMap r => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add, map_add (f := _)]
        exact Submodule.add_mem _ hy hz
      | mul y z _ _ hy hz =>
        rw [Subalgebra.coe_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz)
          (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)
    have hGM : M = G := by
      apply le_antisymm
      · rw [hM, Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        obtain ⟨b, hb0, hbw⟩ := hden w
        obtain ⟨u, hu⟩ := hunit _ hb0
        have h1 : D ℂ L ((b : L) * (w : L)) ∈ G := hB ⟨_, hbw⟩
        rw [Derivation.leibniz] at h1
        have h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G := by
          have h4 := Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))
          convert h4 using 1
          simp [Subalgebra.smul_def]
        have h3 := Submodule.smul_mem G (↑u⁻¹ : O) h2
        rw [← hu, smul_smul, Units.inv_mul, one_smul] at h3
        exact h3
      · rw [hG, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩
    rw [hGM]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    apply hunit
    have hy0 : ev y = 0 := hy
    simp [hy0]
  · rw [hM, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := hmax (w - algebraMap ℂ O (ev w)) (by simp)
    have hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L)) := by
      have h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L) := by
        have h5 := congrArg (fun u : O => (u : L)) ha
        push_cast at h5
        linear_combination h5
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_add (f := _), Derivation.map_algebraMap, zero_add, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.leibniz]
      rfl
    show D ℂ L (w : L) ∈ _
    rw [hD]
    refine Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    · apply Submodule.mem_sup_right
      apply Submodule.smul_mem_smul
      · show ev (t l) = 0
        exact ht l
      · exact Submodule.subset_span ⟨a l, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.locOne_of :
    LocMax → ValBasic → LocOne := by
  intro hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨hle, ⟨ev, hev⟩, hbv, hinv⟩ := hVal L (rB ℂ L (xv x) {0}) e.1
  haveI := hc.smooth 0
  haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance
  have hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b := by
    intro b
    obtain ⟨h, hb⟩ := (hev _ _).1 (hbv b)
    exact hb
  have hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨h0, h1⟩ := hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu
    exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0},
      ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0} := by
    intro v
    obtain ⟨b, hb, hbv'⟩ := v.2
    exact ⟨b, by rw [hevB]; exact hb, hbv'⟩
  let t : Fin d → loc (rB ℂ L (xv x) {0}) e.1 := fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩
  have ht : ∀ l, ev (t l) = 0 := fun l =>
    (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)
  have hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1,
      v = ∑ l, a l * t l := by
    intro v h0
    obtain ⟨a, ha, hv'⟩ := hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)
    refine ⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩
    rw [hv', AddSubmonoidClass.coe_finsetSum]
    rfl
  have hmem := locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  exact ⟨fun l => c l, fun l => (c l).2, hc'.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.POmLoc
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section OmLocAux
variable {L : Type} [Field L] [Algebra ℂ L]

private noncomputable def om1 (B : Subalgebra ℂ L) : Submodule ℂ Ω[L⁄ℂ] :=
  Submodule.span ℂ {w | ∃ b ∈ B, ∃ u ∈ B, w = b • D ℂ L u}

private lemma omB_stab (B : Subalgebra ℂ L) (q : ℕ) {r : L} (hr : r ∈ B) {m : DR ℂ L}
    (hm : m ∈ omB ℂ L B q) : r • m ∈ omB ℂ L B q := by
  have h : omB ℂ L B q ≤ (omB ℂ L B q).comap (Algebra.lsmul ℂ ℂ (DR ℂ L) r) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, v, hv, rfl⟩
    refine Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, ?_⟩
    simp [mul_smul]
  exact h hm

private lemma omB_mono {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) : omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma ι_mul_mem (B : Subalgebra ℂ L) (q : ℕ) {w : Ω[L⁄ℂ]} (hw : w ∈ om1 B) {y : DR ℂ L}
    (hy : y ∈ omB ℂ L B q) : ExteriorAlgebra.ι L w * y ∈ omB ℂ L B (q + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, u, hu, rfl⟩ := hw
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨b * c, B.mul_mem hb hc, Fin.cons u v, fun j => ?_, ?_⟩
      · exact Fin.cases hu hv j
      · rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, mul_smul, Function.comp_def, smul_comm b c]
    | zero => simp
    | add a a' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul t a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ t h
  | zero => simp
  | add a a' _ _ h h' => rw [map_add (f := _), add_mul]; exact Submodule.add_mem _ h h'
  | smul t a _ h => rw [LinearMap.map_smul_of_tower, smul_mul_assoc]; exact Submodule.smul_mem _ t h

private lemma ιMulti_mem (B : Subalgebra ℂ L) (q : ℕ) (w : Fin q → Ω[L⁄ℂ]) (hw : ∀ j, w j ∈ om1 B) :
    ExteriorAlgebra.ιMulti L q w ∈ omB ℂ L B q := by
  induction q with
  | zero =>
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.elim0, fun j => j.elim0, ?_⟩
    rw [one_smul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact ι_mul_mem B q (hw 0) (ih _ fun j => hw _)

private lemma two_mem (B : Subalgebra ℂ L) {b v : L} (hb : b ∈ B) (hv : b * v ∈ B) :
    (b ^ 2) • D ℂ L v ∈ om1 B := by
  have h : (b ^ 2) • D ℂ L v = b • D ℂ L (b * v) - (b * v) • D ℂ L b := by
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, pow_two, mul_comm b v]
    abel
  rw [h]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, _, hv, rfl⟩)
    (Submodule.subset_span ⟨_, hv, b, hb, rfl⟩)

private lemma common_den (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {q : ℕ} {c : L} {v : Fin q → L}
    (hc : c ∈ loc B e) (hv : ∀ j, v j ∈ loc B e) :
    ∃ b : B, e b ≠ 0 ∧ (b : L) * c ∈ B ∧ ∀ j, (b : L) * v j ∈ B := by
  obtain ⟨b0, h0, hc'⟩ := hc
  choose f hf hf' using hv
  refine ⟨b0 * ∏ j, f j, ?_, ?_, fun j => ?_⟩
  · rw [map_mul, map_prod]
    exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hf j)
  · have h := B.mul_mem (∏ j, f j).2 hc'
    convert h using 1
    push_cast
    ring
  · have h := B.mul_mem (b0 * ∏ i ∈ Finset.univ.erase j, f i).2 (hf' j)
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
    convert h using 1
    push_cast
    ring

end OmLocAux

theorem UpperTheory.Gal.productCup_of_system.omLoc_of :
    OmLoc := by
  intro L _ _ B e q
  have hle : B ≤ loc B e := fun v hv => ⟨1, by simp, by simpa using hv⟩
  refine ⟨le_antisymm ?_ ?_, fun r hr m hm => omB_stab B q hr hm, fun B' h => omB_mono h q⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨b, hb, hv⟩
    have hb0 : (b : L) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    have hinv : (b : L)⁻¹ ∈ loc B e := ⟨b, hb, by rw [mul_inv_cancel₀ hb0]; exact B.one_mem⟩
    have h := omB_stab (loc B e) q hinv (omB_mono hle q hv)
    rwa [smul_smul, inv_mul_cancel₀ hb0, one_smul] at h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, v, hv, rfl⟩
    obtain ⟨b, hb, hbc, hbv⟩ := common_den B e hc hv
    refine Submodule.subset_span ⟨b ^ (2 * q + 1), by rw [map_pow]; exact pow_ne_zero _ hb, ?_⟩
    have h1 := ιMulti_mem B q (fun j => ((b : L) ^ 2) • D ℂ L (v j)) fun j => two_mem B b.2 (hbv j)
    have h2 := omB_stab B q hbc h1
    rw [AlternatingMap.map_smul_univ, smul_smul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h2
    convert h2 using 1
    rw [smul_smul]
    congr 1
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PResVal
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section ResValAux
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}

private noncomputable def mono (x : Fin (d + 1) → F) (a : Fin d → ℕ) : F := ∏ l, (x l.succ / x 0) ^ a l

private lemma mono_zero (x : Fin (d + 1) → F) : mono x 0 = 1 := by simp [mono]

private lemma mono_add (x : Fin (d + 1) → F) (a b : Fin d → ℕ) : mono x (a + b) = mono x a * mono x b := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

private lemma mono_closure (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (y : F)
    (hy : y ∈ Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = x j / x i}) :
    ∃ a, y = mono x a := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨i, hi, j, rfl⟩ := hz
    rw [Finset.mem_singleton] at hi
    subst hi
    cases j using Fin.cases with
    | zero => exact ⟨0, by rw [mono_zero, div_self hx]⟩
    | succ l =>
      refine ⟨Pi.single l 1, ?_⟩
      simp only [mono]
      rw [Finset.prod_eq_single l]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  | one => exact ⟨0, (mono_zero x).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (mono_add x a b).symm⟩

private lemma rho_mono (x : Fin (d + 1) → F) (hx : x 0 ≠ 0) (ρ : F →ₗ[ℂ] ℂ) (hρ : IsRes ℂ x ρ) (a : Fin d → ℕ)
    (ha : a ≠ 0) : ρ (mono x a) = 0 := by
  obtain ⟨_, hρ2⟩ := hρ
  set m : Fin (d + 1) → ℤ := Fin.cons (-(∑ l, (a l : ℤ))) (fun l => (a l : ℤ)) with hm
  have hsum : ∑ j, m j = 0 := by
    rw [Fin.sum_univ_succ]
    simp [hm]
  have hne : m ≠ 0 := by
    intro h
    apply ha
    funext l
    simpa [hm] using congrFun h l.succ
  have heq : mono x a = ∏ j, x j ^ m j := by
    rw [Fin.prod_univ_succ]
    simp only [hm, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, mono, div_pow,
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    rw [show (∑ l, (a l : ℤ)) = ((∑ l, a l : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    ring
  rw [heq]
  exact hρ2 m hsum hne

end ResValAux

theorem UpperTheory.Gal.productCup_of_system.resVal_of :
    ValBasic → ResVal := by
  intro hval F K _ _ _ _ _ _ d x hfc ρ hρ e f hf
  obtain ⟨_, _, hBval, _⟩ := hval K (rB ℂ K (xv x) {0}) e.1
  have hx0 : xv x 0 ≠ 0 := (x 0).ne_zero
  have hmemB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F K g ∈ rB ℂ K (xv x) {0} := by
    intro g hg
    exact (isIntegral_algebraMap : IsIntegral (rA ℂ (xv x) {0}) (algebraMap (rA ℂ (xv x) {0}) K ⟨g, hg⟩))
  have hspan : ∀ g, g ∈ rA ℂ (xv x) {0} ↔ g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F) := by
    intro g
    rw [← Algebra.adjoin_eq_span]
    rfl
  have hmono : ∀ (a : Fin d → ℕ) (h : algebraMap F K (mono (xv x) a) ∈ rB ℂ K (xv x) {0}),
      e.1 ⟨_, h⟩ = ρ (mono (xv x) a) := by
    intro a h
    by_cases ha : a = 0
    · subst ha
      have h1 : (⟨algebraMap F K (mono (xv x) 0), h⟩ : rB ℂ K (xv x) {0}) = 1 :=
        Subtype.ext (by simp [mono_zero])
      rw [h1, map_one, mono_zero, hρ.1]
    · rw [rho_mono (xv x) hx0 ρ hρ a ha]
      have h1 : (⟨algebraMap F K (mono (xv x) a), h⟩ : rB ℂ K (xv x) {0}) =
          ∏ l, (⟨algebraMap F K (xv x l.succ / xv x 0), tco_mem ℂ K (xv x) l⟩ : rB ℂ K (xv x) {0}) ^ a l :=
        Subtype.ext (by simp [mono, map_prod, map_pow])
      rw [h1, map_prod]
      obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact ha (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [map_pow, e.2 l, zero_pow hl])
  have key : ∀ g (hg : g ∈ Submodule.span ℂ
      (Submonoid.closure {y | ∃ i ∈ ({0} : Finset (Fin (d + 1))), ∃ j, y = xv x j / xv x i} : Set F))
      (h : algebraMap F K g ∈ rB ℂ K (xv x) {0}), e.1 ⟨_, h⟩ = ρ g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      intro h
      obtain ⟨a, rfl⟩ := mono_closure (xv x) hx0 y hy
      exact hmono a h
    | zero =>
      intro h
      have h1 : (⟨algebraMap F K 0, h⟩ : rB ℂ K (xv x) {0}) = 0 := Subtype.ext (map_zero _)
      rw [h1, map_zero, map_zero]
    | add y z hy hz ihy ihz =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have hz' := hmemB z ((hspan z).2 hz)
      have h1 : (⟨algebraMap F K (y + z), h⟩ : rB ℂ K (xv x) {0}) = ⟨_, hy'⟩ + ⟨_, hz'⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [h1, map_add (f := _), map_add (f := _), ihy hy', ihz hz']
    | smul r y hy ihy =>
      intro h
      have hy' := hmemB y ((hspan y).2 hy)
      have h1 : (⟨algebraMap F K (r • y), h⟩ : rB ℂ K (xv x) {0}) = r • ⟨_, hy'⟩ := by
        apply Subtype.ext
        show algebraMap F K (r • y) = r • algebraMap F K y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
      rw [h1, map_smul, map_smul, ihy hy']
  have hfB := hmemB f hf
  have hv := hBval ⟨_, hfB⟩
  rw [key f ((hspan f).1 hf) hfB] at hv
  exact hv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PValBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)

private theorem mem_loc' {v : L} : v ∈ loc B e ↔ ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B := Iff.rfl

private theorem val_indep {v : L} (b b' c c' : B) (hb : e b ≠ 0) (hb' : e b' ≠ 0)
    (h : (b : L) * v = c) (h' : (b' : L) * v = c') : e c / e b = e c' / e b' := by
  have h1 : b' * c = b * c' := Subtype.ext (by
    push_cast
    rw [← h, ← h']
    ring)
  have h2 := congrArg e h1
  rw [map_mul, map_mul] at h2
  rw [div_eq_div_iff hb hb']
  linear_combination h2

private noncomputable def evF (w : loc B e) : ℂ :=
  e ⟨_, (Classical.choose_spec ((mem_loc' B e).1 w.2)).2⟩ / e (Classical.choose ((mem_loc' B e).1 w.2))

private theorem evF_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evF B e w = e c / e b := by
  obtain ⟨hb0, hc0⟩ := Classical.choose_spec ((mem_loc' B e).1 w.2)
  unfold evF
  exact val_indep B e _ b _ c hb0 hb rfl h

private noncomputable def evH : loc B e →ₐ[ℂ] ℂ where
  toFun := evF B e
  map_one' := by
    rw [evF_eq B e 1 1 1 (by simp) (by simp)]
    simp
  map_zero' := by
    rw [evF_eq B e 0 1 0 (by simp) (by simp)]
    simp
  map_mul' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w * w') (b * b') (⟨_, h⟩ * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_mul, map_mul, mul_div_mul_comm]
  map_add' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w + w') (b * b') (b' * ⟨_, h⟩ + b * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_add, map_mul, map_mul, map_mul]
    field_simp
  commutes' r := by
    rw [evF_eq B e (algebraMap ℂ _ r) 1 (algebraMap ℂ B r) (by simp) (by simp)]
    simp

private theorem evH_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evH B e w = e c / e b :=
  evF_eq B e w b c hb h

end

theorem UpperTheory.Gal.productCup_of_system.valBasic_of :
    ValBasic := by
  intro L _ _ B e
  refine ⟨fun b hb => ⟨1, by simp, by simpa using hb⟩, ⟨evH B e, fun v c => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rintro ⟨b, hb, hbv, h1, h2⟩
    refine ⟨⟨⟨b, hb⟩, h1, hbv⟩, ?_⟩
    rw [evH_eq B e _ ⟨b, hb⟩ ⟨_, hbv⟩ h1 rfl, h2]
    field_simp
  · rintro ⟨h, rfl⟩
    obtain ⟨b, hb, hbv⟩ := (mem_loc' B e).1 h
    refine ⟨b, b.2, hbv, hb, ?_⟩
    rw [evH_eq B e ⟨v, h⟩ b ⟨_, hbv⟩ hb rfl]
    field_simp
  · intro b
    refine ⟨1, B.one_mem, by simp, by simpa using (map_one e).symm ▸ one_ne_zero, ?_⟩
    have h1 : (⟨1, B.one_mem⟩ : B) = 1 := rfl
    have h2 : (⟨1 * (b : L), by simp⟩ : B) = b := Subtype.ext (one_mul _)
    rw [h1, h2, map_one, one_mul]
  · rintro v c ⟨b, hb, hbv, h1, h2⟩ hc
    have h3 : e ⟨b * v, hbv⟩ ≠ 0 := by
      rw [h2]
      exact mul_ne_zero h1 hc
    have hv : v ≠ 0 := by
      rintro rfl
      apply h3
      have : (⟨b * 0, hbv⟩ : B) = 0 := Subtype.ext (mul_zero _)
      rw [this, map_zero]
    refine ⟨hv, ⟨b * v, hbv⟩, h3, ?_⟩
    show b * v * v⁻¹ ∈ B
    rwa [mul_inv_cancel_right₀ hv]
end

