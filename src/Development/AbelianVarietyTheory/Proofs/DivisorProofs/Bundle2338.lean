module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.RatModel.exists_affineOpen_finiteType_int : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  intro o' Ω _ _ _ hB M x
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.Z.isBasis_affineOpens) (show x ∈ (⊤ : M.Z.Opens) from trivial)
  refine ⟨U, hU, hxU, ?_⟩
  have hl := M.lft
  have h1 : (M.s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType M.s hl ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of o')).commRingCatIsoToRingEquiv.symm.surjective
  have h3 : (Int.castRingHom o').FiniteType := by
    have h := hB.ft
    rw [← RingHom.finiteType_algebraMap] at h
    convert h
  have h4 := (h1.comp h2).comp h3
  have he : algebraMap ℤ Γ(M.Z, U) = ((M.s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o')).inv.hom).comp (Int.castRingHom o') := RingHom.ext_int _ _
  rw [← RingHom.finiteType_algebraMap, he]
  exact h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersion
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjSpace

theorem surjective_appLE_of_eq {X Z : Scheme.{0}} {f : Z ⟶ X} {A A' : X.Opens} {B B' : Z.Opens}
    (hA : A = A') (hB : B = B') (h : B ≤ f ⁻¹ᵁ A) (h' : B' ≤ f ⁻¹ᵁ A') :
    Function.Surjective (f.appLE A B h).hom → Function.Surjective (f.appLE A' B' h').hom := by
  subst hA hB
  exact id

theorem exists_affineOpen_fraction_pullRatio : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  intro R _ N Y φ hφ y V i hyV hyi
  obtain ⟨U', hU', hU⟩ := φ.isEmbedding.isInducing.isOpen_iff.1 V.isOpen
  let O : (PSpace R N).Opens := ⟨U', hU'⟩ ⊓ φ.coborderRange
  have hyO : φ y ∈ O := ⟨show φ y ∈ U' by rw [← Set.mem_preimage, hU]; exact hyV, subset_coborder ⟨y, rfl⟩⟩
  obtain ⟨h, hhO, hyh⟩ := (isAffineOpen_chart R N i).exists_basicOpen_le (V := O) ⟨φ y, hyO⟩ hyi
  have hD : IsAffineOpen ((PSpace R N).basicOpen h) := (isAffineOpen_chart R N i).basicOpen h
  have hDc : (PSpace R N).basicOpen h ≤ chart R N i := (PSpace R N).basicOpen_le h
  have hle : (PSpace R N).basicOpen h ≤ φ.coborderRange := fun z hz => (hhO hz).2
  haveI : IsAffine ((PSpace R N).basicOpen h) := hD
  have hp : IsPullback (φ ∣_ (PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h).ι
      ((PSpace R N).homOfLE hle) φ.liftCoborder := by
    refine IsPullback.of_bot (h₃₁ := φ) (v₂₁ := 𝟙 _) (v₂₂ := φ.coborderRange.ι) ?_ ?_ ?_
    · rw [Category.comp_id, Scheme.homOfLE_ι]
      exact isPullback_morphismRestrict φ _
    · rw [← cancel_mono φ.coborderRange.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.Hom.liftCoborder_ι, morphismRestrict_ι]
    · exact IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Scheme.Hom.liftCoborder_ι]⟩
  haveI : IsClosedImmersion (φ ∣_ (PSpace R N).basicOpen h) := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨hWa, hsurj0⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (φ ∣_ (PSpace R N).basicOpen h)
  have hsurj : Function.Surjective
      (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom := by
    rw [Scheme.Hom.appTop, morphismRestrict_app'] at hsurj0
    exact surjective_appLE_of_eq (by simp) (by simp) _ _ hsurj0
  have hWc : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ φ ⁻¹ᵁ chart R N i := φ.preimage_mono hDc
  refine ⟨φ ⁻¹ᵁ (PSpace R N).basicOpen h, hWc, hyh, ?_, hWa, ?_⟩
  · intro z hz
    have : φ z ∈ U' := (hhO hz).1
    rw [← Set.mem_preimage, hU] at this
    exact this
  · intro g
    obtain ⟨a, rfl⟩ := hsurj g
    have hloc := (isAffineOpen_chart R N i).isLocalization_basicOpen h
    have key : ∀ p : MvPolynomial (Fin (N + 1)) R,
        (φ.appLE ((PSpace R N).basicOpen h) (φ ⁻¹ᵁ (PSpace R N).basicOpen h) le_rfl).hom
          (algebraMap Γ(PSpace R N, chart R N i) Γ(PSpace R N, (PSpace R N).basicOpen h)
            (MvPolynomial.aeval (R := R) (ratio R N i) p)) =
        MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) _).hom
          (pullRatio φ _ i hWc) p := by
      intro p
      have e1 := appLE_resG φ hDc (le_rfl : φ ⁻¹ᵁ (PSpace R N).basicOpen h ≤ _) (MvPolynomial.aeval (R := R) (ratio R N i) p)
      have e2 := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ (PSpace R N).basicOpen h) (i := i) (hi := hWc))
      exact e1.trans e2
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a
    obtain ⟨m, hm⟩ := s.2
    obtain ⟨P, rfl⟩ := aeval_ratio_surjective R N i b
    obtain ⟨h₀, hh₀⟩ := aeval_ratio_surjective R N i h
    have hQ : MvPolynomial.aeval (R := R) (ratio R N i) (h₀ ^ m) = (s : Γ(PSpace R N, chart R N i)) := by
      rw [map_pow, hh₀, ← hm]
    refine ⟨P, h₀ ^ m, ?_, ?_⟩
    · rw [← key, hQ]
      exact (IsLocalization.map_units _ s).map _
    · rw [← key, ← key, hQ, ← map_mul]
      exact congrArg _ hs

end GlobalTheory.ProjSpace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPointStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_quotient_pow_lifting_point : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ g : C →+* A, g.comp (algebraMap R C) = ρ →
    ∀ n : ℕ, ∃ f : C →ₐ[R] R ⧸ Ideal.span {t} ^ n, ∀ c : C,
      f c - Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c)) ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t} := by
  first | (exact @GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (exact GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow) | (intros; apply GlobalTheory.GoodEtaleSection.exists_algHom_quot_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBig
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KodairaNefBig

theorem isAffine_of_dim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) :
    IsAffine X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : U = ⊤ := eq_top_iff.2 fun x _ => by
    rw [GlobalTheory.FlagQ.eq_genericPoint_of_krullDim_zero h x]; exact hmem
  subst hU'
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso X.topIso.inv

theorem prod_le {d : ℕ} (q : ℤ) (hq : 1 ≤ q) (n : Fin (d + 1) → Fin 2 → ℤ)
    (h0 : ∀ j, 0 ≤ n 0 j ∧ n 0 j ≤ 2) (hs : ∀ (i : Fin d) j, 0 ≤ n i.succ j ∧ n i.succ j ≤ q)
    (a : Fin (d + 1) → Fin 2) : ∏ i, n i (a i) ≤ 2 * q ^ d := by
  rw [Fin.prod_univ_succ]
  have hp : ∏ i : Fin d, n i.succ (a i.succ) ≤ ∏ _i : Fin d, q :=
    Finset.prod_le_prod₀ (fun i _ => (hs i _).1) fun i _ => (hs i _).2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact mul_le_mul (h0 _).2 hp (Finset.prod_nonneg fun i _ => (hs i _).1) (by norm_num)

end GlobalTheory.KodairaNefBig


open GlobalTheory.KodairaNefBig in
theorem GlobalTheory.exists_ample_add_eff_of_isNef_isBig : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  intro hNN X _ _ p hp N hN hnef hbig
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨D, hD, -⟩ := hbig.growth
  cases D with
  | zero =>
    have := isAffine_of_dim_zero (X := X) (by simpa using hD)
    refine ⟨1, N, hN, 0, one_pos, isAmpleLB_of_isAffine hN, CartierDiv.eff_zero, ?_⟩
    rw [one_smul, ← toPic_apply, map_zero, add_zero]
  | succ d =>
    have := isNoetherian_of_isProjOver hp
    have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℂ X) (GlobalTheory.structureModule X)
      hp' (d := d + 1) (by rw [QCoh.suppDim_structureModule]; exact hD.le)
    let P : Fin 2 → LB X := ![N, A]
    have hPn : ∀ j, IsNef ℂ (P j) := fun j => by
      fin_cases j
      exacts [hnef, hA.isNef]
    have hP : ∀ j, (P j).IsLB := fun j => (hPn j).isLB
    have hI : ∀ a : Fin (d + 1) → Fin 2, 0 ≤ interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
      fun a => hNN.1.interNum_nonneg hp' hD fun i => hPn (a i)
    set S : ℤ := ∑ a : Fin (d + 1) → Fin 2, interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hI a
    have hT : 0 < topSelfIntersection ℂ N (d + 1) := (hNN.2.2.isBig_iff hp' hD hnef).1 hbig
    set q : ℕ := 2 * (d + 1) * S.toNat + 1 with hqdef
    have hqS : (q : ℤ) = 2 * (d + 1) * S + 1 := by
      rw [hqdef]; push_cast [Int.toNat_of_nonneg hS0]; ring
    have hq1 : (1 : ℤ) ≤ q := by rw [hqS]; nlinarith
    let L : LB X := tens A (lbPow N q)
    have hL : IsAmpleLB L := IsAmpleLB.tens_of_isNef hNN ℂ X p hp A _ hA (hnef.pow hA q)
    let B : LB X := lbPow A 2
    have hB : IsAmpleLB B := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
    let M : LB X := tens (lbPow N q) (dual A)
    have hM : M.IsLB := isLB_tens (isLB_lbPow hN q) (isLB_dual hA.isLB)
    have hclsL : cls L hL.isLB = (q : ℤ) • cls N hN + cls A hA.isLB := by
      rw [cls_tens hA.isLB (isLB_lbPow hN q), cls_lbPow hN, natCast_zsmul, add_comm]
    have hclsB : cls B hB.isLB = (2 : ℤ) • cls A hA.isLB := by
      rw [cls_lbPow hA.isLB]; norm_cast
    have hclsM : cls M hM = (q : ℤ) • cls N hN - cls A hA.isLB := by
      rw [cls_tens (isLB_lbPow hN q) (isLB_dual hA.isLB), cls_lbPow hN, cls_dual hA.isLB,
        natCast_zsmul, sub_eq_add_neg]
    have e : cls L hL.isLB = cls M hM + cls B hB.isLB := by
      rw [hclsL, hclsM, hclsB]; abel

    have e₁ := hV.interNum_of_cls_eq_sum hP (Q := fun _ => L) (fun _ => hL.isLB)
      (fun _ => ![(q : ℤ), 1]) (fun _ => by
        rw [Fin.sum_univ_two, hclsL]
        simp [P])
    have hlow : (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) ≤ topSelfIntersection ℂ L (d + 1) := by
      rw [topSelf_def ℂ L, e₁]
      have hnn : ∀ a : Fin (d + 1) → Fin 2,
          0 ≤ (∏ i, (![(q : ℤ), 1] : Fin 2 → ℤ) (a i)) * interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
        fun a => mul_nonneg (Finset.prod_nonneg fun i _ => by
          rcases Fin.exists_fin_two.1 ⟨a i, rfl⟩ with h | h <;> rw [h] <;> simp <;> omega) (hI a)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a)
        (Finset.mem_univ (fun _ => (0 : Fin 2))))
      simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

    let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![0, 2] (fun _ => ![(q : ℤ), 1])
    have e₂ := hV.interNum_of_cls_eq_sum hP (Q := Fin.cons B (fun _ : Fin d => L))
      (Fin.cases hB.isLB fun _ => hL.isLB) n (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_zero, n]
          rw [hclsB]
          simp [P]
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_succ, n]
          rw [hclsL]
          simp [P])
    have hup : interNum ℂ (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
        ≤ 2 * (q : ℤ) ^ d * S := by
      rw [e₂, hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hI a)
      refine prod_le (q : ℤ) hq1 n (fun j => ?_) (fun i j => ?_) a
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n]
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n] <;> omega
    have hineq : ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
        (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection ℂ L (d + 1) := by
      have hqd : (0 : ℤ) < (q : ℤ) ^ d := pow_pos (by omega) d
      have hd1 : (0 : ℤ) ≤ (d : ℤ) + 1 := by positivity
      calc ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
            (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
          ≤ ((d : ℤ) + 1) * (2 * (q : ℤ) ^ d * S) := mul_le_mul_of_nonneg_left hup hd1
        _ = (q : ℤ) ^ d * (2 * (d + 1) * S) := by ring
        _ < (q : ℤ) ^ d * q := mul_lt_mul_of_pos_left (by rw [hqS]; omega) hqd
        _ = (q : ℤ) ^ (d + 1) * 1 := by ring
        _ ≤ (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ topSelfIntersection ℂ L (d + 1) := hlow
    obtain ⟨r, hr, hs⟩ := exists_hasNonzeroSec_pow_of_ample_sub_ample ℂ X hp' d hD.le L B M hL hB hM
      e hineq
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨q * r, lbPow A r, isLB_lbPow hA.isLB r, divOfSec (isLB_lbPow hM r) s hs,
      Nat.mul_pos (Nat.succ_pos _) hr, (isAmpleLB_pow_iff hA.isLB hr).2 hA,
      eff_divOfSec_of_sec _ s hs, ?_⟩
    rw [← toPic_apply, (presents_divOfRatSec _ (isRatSec_ratOfSec s hs)).toPic_eq,
      cls_lbPow hA.isLB, cls_lbPow hM, hclsM]
    first
      | module
      | (simp only [← natCast_zsmul, smul_sub, smul_smul, Nat.cast_mul]; rw [mul_comm (r : ℤ)]; abel)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleNefSmall

theorem mem_nonzeroLocus_secPow_one {X : Scheme.{0}} {L : LB X} (s : L.Sec) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) : x ∈ Out.nonzeroLocus (Cartier.secPow s 1) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  show x ∈ X.basicOpen (resG X (Cartier.lbPow_U L 1 (fun _ => i)).le (s.f i) ^ 1)
  rw [pow_one]
  unfold resG
  rw [Scheme.basicOpen_res]
  exact ⟨(Cartier.lbPow_U L 1 (fun _ => i)).ge (X.basicOpen_le _ hi), hi⟩

end GlobalTheory.AmpleNefSmall

namespace GlobalTheory.AmpleNefSmall


open ProjSpace in
theorem exists_ample_nef_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∃ A : HermLB p, IsAmpleLB A.B ∧ A.IsNef D ∧ ∃ s ∈ A.smallSec, s ≠ 0 := by
  intro hAr k _ X _ p D hX
  obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
  have := hj
  have := hX.finite
  have := isProper_str k N
  have : IsProper p := hjp ▸ inferInstance
  let B : LB X := (O1 k N).pull j
  have hB : B.IsLB := LB.isLB_pull (O1_isLB k N) j
  let c : Fin (N + 1) → B.Sec := fun a => Cartier.secPull (coord k N a) j
  have hc : ⨆ a, Out.nonzeroLocus (c a) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord k N).ge (Opens.mem_top (j x)))
    refine Opens.mem_iSup.2 ⟨a, ?_⟩
    show x ∈ Out.nonzeroLocus (Cartier.secPull (coord k N a) j)
    rw [Cartier.nonzeroLocus_secPull]
    exact ha
  let A₀ : HermLB p := HermLB.fs p hB c hc (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  have hsmall : ∀ a, c a ∈ A₀.smallSec := by
    intro a σ y
    have e (a) : Weight.combVal p σ c 1 a = secVal _ σ (c a) := by
      simp [Weight.combVal, Matrix.one_apply]
    refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := hB) (he := fun a => e a ▸ secVal_mem _)
      (h := Weight.noCommonZero_combVal hc (M := 1) (by simp)) y)
    exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
      (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))
  have hgen : ∀ x : X, CharZero (X.residueField x) →
      ∃ i, x ∈ Out.nonzeroLocus (Cartier.secPow (c i) 1 : (A₀.pow 1).B.Sec) := fun x _ =>
    have ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top x))
    ⟨a, mem_nonzeroLocus_secPow_one _ ha⟩
  obtain ⟨t, ht, hnef⟩ := GlobalTheory.NefOfGen.nef_of_gen hAr k X p D hX A₀ 1 (N + 1)
    (fun i => Cartier.secPow (c i) 1) le_rfl hgen (HermLB.semiPos_fs hB c hc _ _ _)
    (ProjModel.nefFib_of_isAmpleLB A₀ hA)
  refine ⟨A₀.shift (fun _ => t) fun _ => rfl, hA, hnef, ?_⟩
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top (genericPoint X)))
  refine ⟨c a, fun σ y => ?_, fun h0 => ?_⟩
  · refine le_of_eq_of_le (HermLB.nsq_shift A₀ (fun _ => t) (fun _ => rfl) (secVal p σ (c a)) y) ?_
    have h1 := hsmall a σ y
    have h2 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 := Weight.nsq_nonneg (A₀.φ σ) (secVal p σ (c a)) y
    nlinarith
  · have e : c a = (0 : B.Sec) := h0
    rw [e] at ha
    simp [Out.nonzeroLocus] at ha

end GlobalTheory.AmpleNefSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFactor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AHBundle

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ}

theorem mem_of_ex_eq {L L' : LB A.left} (u : HolUnif A L g) (u' : HolUnif A L' g) (hex : u'.ex = u.ex)
    {z : Fin g → ℂ} (hz : z ∈ u.Λ) : z ∈ u'.Λ := by
  rw [← u'.ker, hex, u.ker]; exact hz

theorem isFactorAH_divUnif {M M' : LB A.left} (u : HolUnif A M g) (u' : HolUnif A M' g) (hex : u'.ex = u.ex)
    {H H' : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ}
    (h : IsFactorAH u H χ) (h' : IsFactorAH u' H' χ') :
    IsFactorAH (GlobalTheory.SameFactor.divUnif u u' hex) (H' - H)
      (fun l => χ' ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ / χ l) := by
  refine ⟨h'.1.sub h.1, fun l => ?_, fun l p z hz => ?_⟩
  · have := h.2.1 l
    rw [norm_div, h'.2.1]
    exact (by rw [this]; norm_num : (1 : ℝ) / ‖χ l‖ = 1)
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hl : u.ex (z + l) = u.ex z := by
      rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have e' := h'.2.2 ⟨l.1, mem_of_ex_eq u u' hex l.2⟩ p.1 z (by rw [hex]; exact h1)
    have e := h.2.2 l p.2 z h2
    have n1 := u.fr_ne p.2 z h2
    have n2 := u.fr_ne p.2 (z + l) (by rw [hl]; exact h2)
    have nχ : χ l ≠ 0 := by
      intro h0; have := h.2.1 l; rw [h0, norm_zero] at this; exact zero_ne_one this
    show u'.fr p.1 z * (u.fr p.2 z)⁻¹ = _ * _ * (u'.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹)
    rw [e', e]
    simp only [Matrix.sub_mulVec, dotProduct_sub, mul_sub]
    rw [show ∀ a b c d : ℂ, a - b + (c - d) = (a + c) - (b + d) from fun _ _ _ _ => by ring, Complex.exp_sub]
    have ne := Complex.exp_ne_zero (↑Real.pi * (z ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) +
        ↑Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
    field_simp

end GlobalTheory.AHBundle

theorem GlobalTheory.AHBundle.exists_lb_of_factor_chain {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A]
    (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ) (hL₀ : L₀.IsLB)
    (h₀ : IsFactorAH u₀ H₀ χ₀) (H' : Matrix (Fin g) (Fin g) ℂ)
    (M₁ : LB A.left) (u₁ : HolUnif A M₁ g) (χ₁ : u₁.Λ → ℂ) (hM₁ : M₁.IsLB) (hex₁ : u₁.ex = u₀.ex)
    (h₁ : IsFactorAH u₁ H' χ₁) (k : ℕ) :
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u (H' - k • H₀) χ := by
  induction k with
  | zero => exact ⟨M₁, u₁, χ₁, hM₁, hex₁, by simpa using h₁⟩
  | succ k ih =>
    obtain ⟨M, u, χ, hM, hex, h⟩ := ih
    have hd := GlobalTheory.AHBundle.isFactorAH_divUnif u₀ u hex h₀ h
    have e : H' - (k + 1) • H₀ = (H' - k • H₀) - H₀ := by rw [succ_nsmul, sub_add_eq_sub_sub]
    rw [← e] at hd
    exact ⟨_, _, _, LB.isLB_div hM hL₀, rfl, hd⟩

theorem GlobalTheory.AHBundle.exists_lb_of_hermitian_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g) (H₀ : Matrix (Fin g) (Fin g) ℂ) (χ₀ : u₀.Λ → ℂ), L₀.IsLB → u₀.IsAH H₀ χ₀ →
    ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian →
    (∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (M : LB A.left) (u : HolUnif A M g) (χ : u.Λ → ℂ), M.IsLB ∧ u.ex = u₀.ex ∧ IsFactorAH u Hm χ := by
  intro g A _ hA L₀ u₀ H₀ χ₀ hL₀ hAH Hm hHm hint
  obtain ⟨n, hn⟩ := (_root_.GlobalTheory.posn_main) g H₀ Hm hAH.2.1
  have hint0 := (_root_.GlobalTheory.TorusRM.ahFactor_im_int) g A L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
  have hint' : ∀ l ∈ u₀.Λ, ∀ l' ∈ u₀.Λ, ∃ m : ℤ, (l ⬝ᵥ (Hm + n • H₀).mulVec (star l')).im = m := by
    intro l hl l' hl'
    obtain ⟨m₁, e₁⟩ := hint l hl l' hl'
    obtain ⟨m₂, e₂⟩ := hint0 l hl l' hl'
    refine ⟨m₁ + n * m₂, ?_⟩
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, Complex.add_im,
      nsmul_eq_mul, Complex.mul_im, e₁, e₂]
    push_cast; simp
  have hH' : (Hm + n • H₀).IsHermitian := hHm.add (by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_nsmul, hAH.1.eq])
  obtain ⟨M₁, u₁, χ₁, hM₁, hex₁, h₁⟩ := (_root_.GlobalTheory.AHPos.exists_lb_of_posDef) g A hA L₀ u₀ H₀ χ₀ hL₀ hAH (Hm + n • H₀) hH' hn hint'
  obtain ⟨M, u, χ, hM, hex, h⟩ := GlobalTheory.AHBundle.exists_lb_of_factor_chain L₀ u₀ H₀ χ₀ hL₀ (isFactorAH_of_isAH hAH)
    _ M₁ u₁ χ₁ hM₁ hex₁ (isFactorAH_of_isAH h₁) n
  refine ⟨M, u, χ, hM, hex, ?_⟩
  simpa using h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback : ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → ∀ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ → (∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) → ∀ (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsSquare f₁ f₂ → ∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ)) := by
  first | exact @GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | exact GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | (intros; apply GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam <;> assumption)
end

