module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrime
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum.OscInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}


open Classical in
theorem two_mul_card_psi_le :
    2 * (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ Module.finrank ℚ E := by
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro h
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, Complex.mul_re, him] at h2
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [sq_nonneg H.rt0.re]
  have hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      unfold InPsi at hτ ⊢
      simp only [RingHom.coe_comp, Function.comp_apply, hτ]
      exact hne
    · intro τ _ σ _ h
      ext x
      have := congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h
      simpa using this
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => InPsi H τ)
  rw [Finset.card_univ, NumberField.Embeddings.card] at htot
  omega


open Classical in
theorem card_big_fiber_le {Dw : Datum H} {F k m : ℕ} (hS : Shape Dw F k m) (τ : E →+* ℂ) :
    (Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card ≤ m + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  calc _ ≤ (Finset.Ico (k - 2) Dw.p).card := by
        refine Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_
        · intro f hf
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢
          obtain ⟨⟨hpsi, hk⟩, -⟩ := hf
          have hlt := f.2.isLt
          have hm : Dw.mult f.1 = Dw.p := if_pos hpsi
          have hk' : k ≤ f.2.val + 1 + 1 := hk
          omega
        · intro f hf g hg hfg
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hf hg
          obtain ⟨τ1, j1⟩ := f
          obtain ⟨τ2, j2⟩ := g
          obtain ⟨-, h1'⟩ := hf
          obtain ⟨-, h2'⟩ := hg
          simp only at h1' h2' hfg
          subst h1' h2'
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hfg))
    _ ≤ m + 1 := by rw [Nat.card_Ico]; omega

theorem boundFine_le {p N q i c m M : ℕ} (hp : 2 ≤ p) (hq : q ≤ m) (hi : N ≤ m + i) (hiN : i ≤ N) (hc : 1 ≤ c)
    (hcM : c ≤ M) :
    boundFine p N q i c ≤ (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) + (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hi' : (N : ℝ) ≤ m + i := by exact_mod_cast hi
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb p c := Real.logb_nonneg (by linarith) hc'
  have hl : Real.logb p c ≤ Real.logb p M := Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hcm : (0 : ℝ) ≤ c * m := by positivity
  have t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1) := by
    calc _ ≤ (c : ℝ) * m * p / ((p : ℝ) ^ 2 - 1) := by
          gcongr
          linarith
      _ ≤ _ := by
          rw [div_le_div_iff₀ hp2 hp1]
          nlinarith [mul_nonneg hcm hp1.le]
  have t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤
      c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by
    gcongr
  have t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
    gcongr
  have e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) =
      c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by ring
  unfold boundFine
  linarith


open Classical in
theorem sum_bound_le {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} {p : ℕ}
    (hS : Shape Dw F k m) (hB : ExpBd Dw k cx Mb Sm M) (hp : 2 ≤ p) (hM : 1 ≤ M) :
    ∑ f, (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))
      ≤ eSmall F (Dw.p + Dw.q) m Mb Sm M p := by
  have hfib := card_big_fiber_le hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  obtain ⟨hMb, hτ, hSm, hcM⟩ := hB
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) (by exact_mod_cast hM)
  have hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F := by
    have := two_mul_card_psi_le (H := H)
    omega
  have hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F := by exact_mod_cast hF
  set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX
  set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f),
      f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ) := fun f hf =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩
  have hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), ((cx f : ℝ) * X + Y) ≤
      F * (Mb * X + (m + 1) * Y) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), (Mb * X + (m + 1) * Y) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          have a1 := hτ τ
          have a2 : ((Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1 := by
            exact_mod_cast hfib τ
          rw [Nat.cast_sum] at a1
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)
          · convert a1
          · convert a2
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hF' (by positivity)
  have hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), boundAll p (rk f) (cx f) ≤
      Sm / ((p : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)
    unfold sumSmallSpread boundAll
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]
    ext f
    simp only [Finset.mem_filter, not_isBig_iff]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => IsBig k f)]
  have e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1) := by
    rw [hX, hY]
    unfold eSmall
    ring
  rw [e]
  refine add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)
  · have hb : IsBig k f := (Finset.mem_filter.1 hf).2
    have hm : Dw.mult f.1 = Dw.p := if_pos hb.1
    have hr := rk_le f
    have hk := hb.2
    split_ifs with h
    · exact boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)
    · have h0 : cx f = 0 := by
        by_contra hne
        exact h ⟨hb, by omega⟩
      simp [boundAll, h0, hY0]
  · exact Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1

end GlobalTheory.RefSum.OscInert

namespace GlobalTheory.RefSum

theorem oscLe_eSmall_of_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la
  classical
  have key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤
      (if IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f)) := by
    intro f
    split_ifs with h
    · exact _root_.GlobalTheory.RefSum.facBetween_fine E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2
    · exact ⟨0, _, (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩
  choose A B hAB hle using key
  obtain ⟨-, n, hn⟩ := (GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB
  have h1 := OscInert.sum_bound_le hS hB hp.out.two_le hM
  have h2 := (Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)
  exact ⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionZeroCase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.DimZero

section Basics

variable {R : Type} [CommRing R] [IsDomain R]

theorem isIso_hom (D : DegPre R) (hg : D.P.g = 0) : IsIso D.P.A.hom :=
  GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)

theorem hom_subsingleton (D : DegPre R) (hg : D.P.g = 0) (T : Over (Sp R)) : Subsingleton (T ⟶ D.P.A) := by
  haveI := isIso_hom D hg
  refine ⟨fun f f' => Over.OverMorphism.ext ?_⟩
  rw [← cancel_mono D.P.A.hom, Over.w f, Over.w f']

theorem subsingleton_A {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : Subsingleton N.A := by
  haveI := hom_subsingleton D hg (TF (R := R) F)
  exact ⟨fun x y => ν.eA.injective (Subsingleton.elim _ _)⟩

theorem th_one_ne_zero {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R} {N : NumD F} (ν : NumOf D F N)
    (hg : D.P.g = 0) : N.th 1 ≠ 0 := by
  haveI : IsIso D.P.A.hom := isIso_hom D hg
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := GlobalTheory.MBLow.AbKey.exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  intro h0
  have h := ν.th_eq 1
  rw [h0, zero_mul] at h
  have hU : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ D.P.L.U (ν.J (ν.eA 1).left) := ν.good _
  have hx : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      (fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) := fun y hy => Set.mem_iInter.2 fun _ => by
    rw [Category.comp_id]; exact hU hy
  unfold sF valF at h
  rw [dite_eq_left hx] at h
  exact (((hu _).map _).map _).ne_zero h.symm

end Basics

section Classical

variable {g : ℕ}

theorem dot_empty [IsEmpty (Fin g)] (u v : Fin g → ℂ) : u ⬝ᵥ v = 0 := by
  simp [dotProduct]

theorem thetaChar_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b z : Fin g → ℂ) :
    thetaChar τ a b z = 1 := by
  unfold thetaChar
  rw [tsum_fintype, Fintype.sum_unique]
  simp [dot_empty]

theorem autV_empty [IsEmpty (Fin g)] (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    autV τ a b M N z = 1 := by
  simp [autV, dot_empty]

theorem posDef_empty [IsEmpty (Fin g)] (A : Matrix (Fin g) (Fin g) ℝ) : A.PosDef :=
  ⟨by ext i; exact isEmptyElim i, fun x hx => (hx (Subsingleton.elim _ _)).elim⟩

theorem differentiableOn_empty [IsEmpty (Fin g)] (f : (Fin g → ℂ) → ℂ) (s : Set (Fin g → ℂ)) :
    DifferentiableOn ℂ f s := fun x _ =>
  ((hasFDerivAt_const (f x) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => congrArg f (Subsingleton.elim y x))).differentiableAt.differentiableWithinAt

def abZero (B : NumB ℂ) (g : ℕ) (hg : g = 0) (hA : Subsingleton B.A) (hth : B.th 1 ≠ 0) : AB B g where
  τ := 0
  a := 0
  b := 0
  c := B.th 1
  symm := by ext i; haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  pos := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact posDef_empty _
  ha i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hb i := by haveI : IsEmpty (Fin g) := hg ▸ inferInstance; exact isEmptyElim i
  hc := hth
  ex _ := 1
  ex_add _ _ := (mul_one 1).symm
  onto x := ⟨0, Subsingleton.elim _ _⟩
  ker z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    exact ⟨fun _ => ⟨0, 0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  fr _ := 1
  fr_zero := rfl
  fr_per M N z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [autV_empty]
  th z := by
    haveI : IsEmpty (Fin g) := hg ▸ inferInstance
    simp [thetaChar_empty]

end Classical

section Geo

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem valF_eq_valR {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := rfl

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) : (res e u).val = resG X e u.val := rfl

def frZ (ν : NumOf D ℂ N) (i : D.P.L.ι) : ℂ :=
  valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U (ν.J (ν.eA 1).left)) (D.P.L.g i (ν.J (ν.eA 1).left)).val * ν.rg

theorem frZ_compat (ν : NumOf D ℂ N) (i j : D.P.L.ι) (h : ⊤ ≤ (ν.eA 1).left ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j)) :
    frZ ν i = valF (ν.eA 1).left (D.P.L.U i ⊓ D.P.L.U j) (D.P.L.g i j).val * frZ ν j := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have h3 : ⊤ ≤ x ⁻¹ᵁ (D.P.L.U i ⊓ D.P.L.U j ⊓ D.P.L.U k) := fun y hy => ⟨h hy, hk hy⟩
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.cocycle i j k)
  simp only [Units.val_mul] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_mul x _ h3, val_res, val_res, val_res, GlobalTheory.ZH.CrdCalc.valR_res x _ h3,
    GlobalTheory.ZH.CrdCalc.valR_res x _ h3, GlobalTheory.ZH.CrdCalc.valR_res x _ h3] at c
  simp only [valF_eq_valR]
  rw [← c]
  ring

theorem frZ_self (ν : NumOf D ℂ N) : frZ ν (ν.J (ν.eA 1).left) = ν.rg := by
  unfold frZ
  set x := (ν.eA 1).left
  set k := ν.J x
  have hk : ⊤ ≤ x ⁻¹ᵁ D.P.L.U k := ν.good x
  have c := congrArg (fun u => valR x _ (Units.val u)) (D.P.isLB.g_self k)
  simp only [val_res, Units.val_one] at c
  rw [GlobalTheory.ZH.CrdCalc.valR_res x _ hk, GlobalTheory.ZH.CrdCalc.valR_eq x _ hk, map_one] at c
  rw [valF_eq_valR, c, _root_.one_mul]

theorem isD_zero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (b : TE R ℂ ⟶ D.P.A) : IsD ν d 0 b := by
  haveI := hom_subsingleton D hg (TE R ℂ)
  intro U f hU
  have hb : b = (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0) :=
    Subsingleton.elim _ _
  have hl : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    rw [hb]
    have e : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        ((Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫ ν.eA (d.ex 0)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id]
    rw [e]
    rfl
  rw [hl, (GlobalTheory.ZH.CrdCalc.valR_spMap _ _ U hU).2, map_zero, TrivSqZeroExt.inr_zero, add_zero,
    TrivSqZeroExt.algebraMap_eq_inl]
  rfl

def geoZero (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB g) (hg' : g = 0) (hex : ∀ z, d.ex z = 1)
    (hfr : ∀ z, d.fr z = 1) : Geo ν d where
  frG i _ := frZ ν i
  hol U f := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact ⟨isOpen_discrete _, differentiableOn_empty _ _⟩
  fr_hol i := by
    haveI : IsEmpty (Fin g) := hg' ▸ inferInstance
    exact differentiableOn_empty _ _
  fr_compat i j z h := by
    rw [hex] at h ⊢
    exact frZ_compat ν i j h
  fr_eq z := by
    rw [hex, hfr, Units.val_one, _root_.one_mul]
    exact (frZ_self ν).symm
  dif b _ := ⟨0, isD_zero ν hg d b⟩

end Geo

section Main

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}

theorem keyOK_zero (κ : Rule) (ν : NumOf D ℂ N) (hg : D.P.g = 0) (d : AB N.toNumB D.P.g) (hc : d.c = N.th 1) :
    KeyOK κ ν d := by
  intro vB b MB k₀ _ _ _ hk
  haveI : IsEmpty (Fin D.P.g) := hg ▸ inferInstance
  rw [Matrix.det_isEmpty, one_pow, hc, mul_comm]
  exact ⟨one_ne_zero, hk.1 hg⟩

theorem main : ∀ κ : Rule, AllC fun {R} _ _ {D} _ {N} ν => D.P.g = 0 →
    ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), KeyOK κ ν d := by
  intro κ R _ _ _ _ D _ _ _ N ν hg
  let d := abZero N.toNumB D.P.g hg (subsingleton_A ν hg) (th_one_ne_zero ν hg)
  exact ⟨d, geoZero ν hg d hg (fun _ => rfl) (fun _ => rfl), keyOK_zero κ ν hg d rfl⟩

end Main

end GlobalTheory.MBLow.DimZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBase
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interNumRed_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  intro F _ Y W y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hemb := W.δ.isClosedEmbedding
  have hcl : Set.range W.δ = closure {W.δ (genericPoint Y.X)} := by
    rw [← Set.image_singleton, hemb.closure_image_eq, genericPoint_spec Y.X, Set.image_univ]
  have hf : ∀ r : F, W.δ.appTop (algebraMap F Γ(W.Z, ⊤) r) = algebraMap F Γ(Y.X, ⊤) r := fun r => by
    show W.δ.appTop ((W.p₁ ≫ Y.str).appTop ((Scheme.ΓSpecIso (.of F)).inv r)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, W.δ₁, Category.id_comp]
    rfl
  show interNumRed F _ _ = _
  rw [InterModel.interNumRed_eq_interNumOn F W.δ _ hcl, interNumOn_eq_interNum_pull hf fun i => isLB_toLB (y i)]
  refine (interNum_congr_cls F _ (fun i => isLB_toLB (e i)) (fun i => LB.isLB_pull (isLB_toLB (y i)) _) fun i => ?_).symm
  rw [cls_pull (isLB_toLB (y i))]
  rcases h i with h | h
  · rw [← PullPres.pull_cls_toLB _ _ W.p₁ _ _ h, ← CechPic.pull_comp, W.δ₁, CechPic.pull_id]
  · rw [← PullPres.pull_cls_toLB _ _ W.p₂ _ _ h, ← CechPic.pull_comp, W.δ₂, CechPic.pull_id]

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliserStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigen_inertPlace_latticeStabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.VDblEig.vdbl_eigen | exact GlobalTheory.VDblEig.vdbl_eigen | (intros; apply GlobalTheory.VDblEig.vdbl_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  first | exact @GlobalTheory.CompHS.exists_frPt_of_flagOpen | exact GlobalTheory.CompHS.exists_frPt_of_flagOpen | (intros; apply GlobalTheory.CompHS.exists_frPt_of_flagOpen <;> assumption)
end

