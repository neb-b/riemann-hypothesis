module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.FiniteSubfamilySpansDual
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.finite_subfamily_spans_dual {E Y : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (f : Y → Module.Dual ℝ E) (S : Set Y) :
    ∃ M : Finset Y, M.card ≤ Module.finrank ℝ E ∧ (∀ y ∈ M, y ∈ S) ∧
      ∀ k : E, (∀ y ∈ M, f y k = 0) → ∀ y ∈ S, f y k = 0 := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ (f '' S)
  have hbfin : b.Finite := hli.setFinite
  have hch : ∀ φ ∈ b, ∃ y, y ∈ S ∧ f y = φ := fun φ hφ => hbs hφ
  choose g hgS hgf using hch
  refine ⟨hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2)), ?_, ?_, ?_⟩
  · haveI : Fintype b := hbfin.fintype
    calc (hbfin.toFinset.attach.image (fun φ => g φ.1 (hbfin.mem_toFinset.mp φ.2))).card
        ≤ hbfin.toFinset.attach.card := Finset.card_image_le
      _ = hbfin.toFinset.card := Finset.card_attach
      _ = Fintype.card b := hbfin.card_toFinset
      _ ≤ Module.finrank ℝ (Module.Dual ℝ E) := hli.fintype_card_le_finrank
      _ = Module.finrank ℝ E := Subspace.dual_finrank_eq
  · intro y hy
    obtain ⟨φ, _, rfl⟩ := Finset.mem_image.mp hy
    exact hgS _ _
  · intro k hk y hy
    have hsub : b ⊆ LinearMap.ker (Module.Dual.eval ℝ E k) := by
      intro φ hφ
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply, ← hgf φ hφ]
      exact hk _ (Finset.mem_image.mpr ⟨⟨φ, hbfin.mem_toFinset.mpr hφ⟩, Finset.mem_attach _ _, rfl⟩)
    have hle := Submodule.span_le.mpr hsub
    rw [hspan] at hle
    have hm := hle (Submodule.subset_span ⟨y, hy, rfl⟩)
    rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at hm

theorem UpperTheory.V.KT.vxdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    ∃ M : Finset (Lat L N), M.card ≤ dd L N * N ∧ (∀ y ∈ M, q v.1 y = 1) ∧
      ∀ h : HS L N, (∀ y ∈ M, q h y = 1) → h = v.1 := by
  intro L _ _ _ N v
  obtain ⟨M, hMc, hMS, hMk⟩ := UpperTheory.V.KT.finite_subfamily_spans_dual (E := HS L N)
    (fun y : Lat L N => (ev y : Module.Dual ℝ (HS L N))) {y | y ≠ 0 ∧ q v.1 y = 1}
  refine ⟨M, hMc.trans (rankhs L N), fun y hy => (hMS y hy).2, ?_⟩
  intro h hh
  have hk : ∀ y ∈ M, ev y (h - v.1) = 0 := by
    intro y hy
    rw [map_sub, ev_apply, ev_apply, hh y hy, (hMS y hy).2, sub_self]
  have hall := hMk (h - v.1) hk
  have h0 : h - v.1 = 0 := by
    apply v.2.2
    intro y hy
    have hy' : q v.1 y.1 = 1 := by
      rw [← ev_apply]
      exact hy
    exact hall y.1 ⟨y.2, hy'⟩
  exact sub_eq_zero.mp h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfone
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (I : ℕ), 0 < I →
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  classical
  intro L _ _ N I hI
  have hr0 : (I : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hI.ne'
  have hcardQ : Nat.card (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = I ^ Module.finrank ℚ L := by
    have h1 := Ideal.absNorm_span_singleton (I : 𝓞 L)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [h1, ← map_natCast (algebraMap ℤ (𝓞 L)) I, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  haveI : Finite (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero _ hI.ne')
  letI : Fintype (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) := Fintype.ofFinite _
  have hB : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ nrmDet A = I →
      ∃ B, A * B = (I : 𝓞 L) • 1 ∧ B * A = (I : 𝓞 L) • 1 := by
    intro A hA
    obtain ⟨_, B, h1, h2⟩ := scinv L N A hA.1
    rw [hA.2] at h1 h2
    exact ⟨B, h1, h2⟩
  let key : Matrix (Fin N) (Fin N) (𝓞 L) → Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    fun A => if h : A.det ≠ 0 ∧ nrmDet A = I then
      (Classical.choose (hB A h)).map (Ideal.Quotient.mk _) else 0
  let rep : Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) → Matrix (Fin N) (Fin N) (𝓞 L) :=
    fun k => if h : ∃ A, (A.det ≠ 0 ∧ nrmDet A = I) ∧ key A = k then Classical.choose h else 0
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ]
    change Fintype.card (Fin N → Fin N → 𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardQ,
      dd, ← pow_mul, ← pow_mul, mul_assoc]
  · intro A hdet hnrm
    have hA : A.det ≠ 0 ∧ nrmDet A = I := ⟨hdet, hnrm⟩
    have hex : ∃ A', (A'.det ≠ 0 ∧ nrmDet A' = I) ∧ key A' = key A := ⟨A, hA, rfl⟩
    have hrep : rep (key A) = Classical.choose hex := dif_pos hex
    obtain ⟨hA'P, hA'k⟩ := Classical.choose_spec hex
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hB A hA)
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (hB _ hA'P)
    have hkk : (Classical.choose (hB _ hA'P)).map (Ideal.Quotient.mk (Ideal.span {(I : 𝓞 L)})) =
        (Classical.choose (hB A hA)).map (Ideal.Quotient.mk _) := by
      have keyeq : ∀ (M : Matrix (Fin N) (Fin N) (𝓞 L)) (h : M.det ≠ 0 ∧ nrmDet M = I),
          key M = (Classical.choose (hB M h)).map (Ideal.Quotient.mk _) := fun M h => dif_pos h
      exact (keyeq _ hA'P).symm.trans (hA'k.trans (keyeq A hA))
    have hent : ∀ i j, ∃ x, Classical.choose (hB A hA) i j - Classical.choose (hB _ hA'P) i j =
        (I : 𝓞 L) * x := by
      intro i j
      have h := congrFun (congrFun hkk i) j
      simp only [Matrix.map_apply] at h
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨-c, by rw [mul_neg, ← hc, neg_sub]⟩
    choose X hX using hent
    obtain ⟨g, hg⟩ := hnfeq (𝓞 L) N (I : 𝓞 L) hr0 A (Classical.choose hex) _ _ (Matrix.of X)
      h1 h2 h1' h2' (by ext i j; simp [hX])
    refine ⟨g, ?_⟩
    rw [hg, Finset.mem_image]
    exact ⟨key A, Finset.mem_univ _, hrep⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.locfin :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N → ∀ B : ℝ,
    ∃ S : Set (Lat L N), S.Finite ∧ ∀ᶠ k in nhds h, ∀ y ∉ S, B < q k y := by
  intro L _ _ N h hh B
  obtain ⟨c, hc, hev⟩ := lowbd L N h hh
  obtain ⟨R, hR⟩ := exists_nat_gt (max (B / c) 1)
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRB : B / c < R := lt_of_le_of_lt (le_max_left _ _) hR
  set T := {a : 𝓞 L | ∀ w : InfinitePlace L, ‖embO w a‖ ≤ (R : ℝ)} with hT
  refine ⟨Set.pi Set.univ (fun _ => T), Set.Finite.pi (fun _ => (cntconj L R).1), ?_⟩
  filter_upwards [hev] with k hk
  intro y hy
  have hy' : ∃ a w, (R : ℝ) < ‖embO w (y a)‖ := by
    by_contra hne
    push_neg at hne
    exact hy (fun a _ w => hne a w)
  obtain ⟨a, w, hlt⟩ := hy'
  have hle : ‖embO w (y a)‖ ≤ ‖toR y‖ :=
    (norm_le_pi_norm (toR y w) a).trans (norm_le_pi_norm (toR y) w)
  have hzR : (R : ℝ) < ‖toR y‖ := hlt.trans_le hle
  have hz1 : (1 : ℝ) ≤ ‖toR y‖ := hR1.le.trans hzR.le
  have hsq : ‖toR y‖ ≤ ‖toR y‖ ^ 2 := by nlinarith
  have hB : B < c * ‖toR y‖ := by
    rw [div_lt_iff₀ hc] at hRB
    nlinarith
  exact lt_of_lt_of_le (hB.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)) (hk (toR y))
end

