module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.Bundle0007
public import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypotheses

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAtBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 TopologicalSpace

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RelAmpleFixed

theorem veryAmpleAt_baseChange : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] [IsCommMonObj B] (M : LB B.left),
    IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ k : ℕ, 1 ≤ k ∧ ∀ (R' : Type) [CommRing R'] (φ : Rg →+* R')
      (B' : Over (Sp R')) [GrpObj B'] (φB : B'.left ⟶ B.left), IsGrpPullback B' B (spMap φ) φB →
      Out.VeryAmpleAt B' (M.pull φB) k := by
  intro Rg _ B _ _ L _ hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  refine ⟨N, hN, fun R' _ fr B' _ φ hg => ?_⟩
  have h : IsPullback φ B'.hom B.hom (spMap fr) := hg.1
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw'⟩ := PolBaseChange.lbIso_refl hL'
  have hw := (isGen_iff w).1 hw'
  intro U' hU'
  have le : U' ≤ (spMap fr) ⁻¹ᵁ (⊤ : (Sp Rg).Opens) := fun y _ => trivial
  have le' : B'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (B.hom ⁻¹ᵁ ⊤) := fun y _ => trivial
  let ψ := φ.resLE (B.hom ⁻¹ᵁ ⊤) (B'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (B.hom ⁻¹ᵁ ⊤).ι = (B'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (B'.hom ∣_ U') (B.hom ∣_ ⊤) ((spMap fr).resLE ⊤ U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict B.hom ⊤).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict B'.hom U').flip.paste_horiz h
    · rw [← cancel_mono (⊤ : (Sp Rg).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w,
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine (⊤ : (Sp Rg).Opens) := isAffineOpen_top _
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := linComb_isLB (L.pull φ) hL' (K := Fin N) (fun _ => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver B L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map (((spMap fr).resLE ⊤ U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.RelAmpleFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceCoefficientSpaceEqExtremalTensorLine
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory.CoefWtLine

open Formalism.GradedWeylDivisibility


open Classical in
def blkW (ι : Type) (n : ℕ) : ι × Fin n × Fin n → ι → Fin n → ℕ :=
  fun v => Pi.single v.1 (Pi.single v.2.1 1)

theorem weight_blkW {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n × Fin n →₀ ℕ) (τ : ι) (a : Fin n) :
    Finsupp.weight (blkW ι n) m τ a = ∑ s : Fin n, m (τ, a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_eq_single τ, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, hb]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [blkW, hb]
  · simp

open Classical in
theorem blockEmb_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (τ : ι)
    (f : MvPolynomial (Fin n × Fin n) K) (μ : Fin n → ℕ) (hf : IsWeightedHomogeneous (rowW n n) f μ) :
    IsWeightedHomogeneous (blkW ι n) (blockEmb K τ f) (Pi.single τ μ) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  have e := hf hu
  funext τ' a
  rw [weight_blkW]
  by_cases h : τ' = τ
  · subst h
    rw [Pi.single_eq_same, ← e, GlobalTheory.LvT.KerLat.weight_rowW, rowDeg]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (fun x y hxy => (Prod.mk.inj hxy).2) u (a, s)
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun s _ => ?_
    apply Finsupp.mapDomain_notin_range
    rintro ⟨x, hx⟩
    exact h (Prod.mk.inj hx).1.symm

theorem ten_hom {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
    (f : ι → MvPolynomial (Fin n × Fin n) K) (μ : ι → Fin n → ℕ)
    (hf : ∀ τ, IsWeightedHomogeneous (rowW n n) (f τ) (μ τ)) :
    IsWeightedHomogeneous (blkW ι n) (ten f) μ := by
  classical
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ => blockEmb K τ (f τ)) _
    (fun τ _ => blockEmb_hom τ (f τ) (μ τ) (hf τ))
  have e : μ = ∑ τ, Pi.single τ (μ τ) := (Finset.univ_sum_single μ).symm
  rw [e]
  exact h

theorem natW_antitone' {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

theorem extremal_hom (K : Type) [Field K] {n : ℕ} (l : DomWeight n) :
    IsWeightedHomogeneous (rowW n n) (extremal K n l) l.natW := by
  have h := hwRowWeight K n n le_rfl l.natW (natW_antitone' l)
  have e : (rowNu l.natW : Fin n → ℕ) = l.natW := by
    funext a
    simp [rowNu]
  rwa [e] at h

theorem weight_line : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n), (∀ m ∈ (ten fun τ => extremal K n (lam τ) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) ∧ ∀ G ∈ VV K lam, (∀ m ∈ G.support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∃ c : K, G = c • ten fun τ => extremal K n (lam τ) := by
  intro K _ ι _ n lam
  classical
  refine ⟨fun m hm τ a => ?_, fun G hG hw => ?_⟩
  · have h := ten_hom _ (fun τ => (lam τ).natW) (fun τ => extremal_hom K (lam τ)) (mem_support_iff.1 hm)
    rw [← weight_blkW, h]
  · have hGh : IsWeightedHomogeneous (blkW ι n) G (fun τ => (lam τ).natW) := by
      intro d hd
      funext τ a
      rw [weight_blkW]
      exact hw d (mem_support_iff.2 hd) τ a
    have key : VV K lam ≤ (Submodule.span K {(ten fun τ => extremal K n (lam τ) : Pol K ι n)}).comap
        (weightedHomogeneousComponent (blkW ι n) (fun τ => (lam τ).natW)) := by
      rw [← (bVVfun_spec K lam).2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have sp := fun τ => (sSBasis K n n (lam τ).natW).choose_spec.1
      have hb : ∀ τ, IsWeightedHomogeneous (rowW n n) (ssB K (lam τ).natW (i τ)) (rowWt (i τ).1) :=
        fun τ => (sp τ).2.2 (i τ)
      have hi : IsWeightedHomogeneous (blkW ι n) (bVVfun K lam i) (fun τ => rowWt (i τ).1) := ten_hom _ _ hb
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      by_cases he : (fun τ => (lam τ).natW) = fun τ => rowWt (i τ).1
      · rw [← he] at hi
        rw [hi.weightedHomogeneousComponent_same]
        have hc : ∀ τ, ∃ c : K, ssB K (lam τ).natW (i τ) = c • extremal K n (lam τ) := fun τ => by
          refine GlobalTheory.Alc.hw_line_field K n _ (natW_antitone' _) _ ?_ ?_
          · rw [← (sp τ).2.1]
            exact Submodule.subset_span ⟨i τ, rfl⟩
          · have := hb τ
            rwa [← congrFun he τ] at this
        choose c hc using hc
        refine Submodule.mem_span_singleton.2 ⟨∏ τ, c τ, ?_⟩
        simp only [bVVfun, ten, hc, map_smul]
        exact (Finset.prod_smul _ _ _).symm
      · rw [hi.weightedHomogeneousComponent_ne _ he]
        exact zero_mem _
    have h := key hG
    rw [Submodule.mem_comap, hGh.weightedHomogeneousComponent_same] at h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨c, hc.symm⟩

end GlobalTheory.CoefWtLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe {N : ℕ} (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    (eV N ν a b x : MvPolynomial (Fin N × Fin N) ℚ) = LR.der N N a b x := by
  unfold eV
  rw [dite_eq_left ⟨a.2, b.2⟩]
  rfl

theorem cut_incl (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ K w Λ : ℕ)
    (h₁ : ∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)),
      (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i)))
    (h₂ : ∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
      (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j)))
    (hK : ∀ i j, ν i ≤ ν j + K) (hw' : K + (p + q) ≤ w + 1)
    (hΛ : ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) :
    ∀ x ∈ dualWeyl ℤ (p + q) (p + q) ν, ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x ∈ weyl ℤ (p + q) (p + q) le_rfl ν := by
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hL p q ν hν c₁ c₂ h₁ h₂
  obtain ⟨hrel, hspan, hdom, hst1, hst2⟩ := hN (p + q) ν hν
  obtain ⟨hrel', hbdd'⟩ := hA _ (p + q) K _ hrel (hB (p + q) ν hν K hK) hspan
  set e := eV (p + q) ν with he
  set S₀ := gridP (fun c d => adj (e c d)) K p q p T with hS₀
  have hinv : ∀ c < p + q, ∀ d < p + q, adj (e c d) S₀ = 0 :=
    hG _ p q K _ hrel' hbdd' T (fun c hc d hd hcd => by
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hT1 c hc d hd hcd, sub_self])
  let v : dualWeyl ℚ (p + q) (p + q) ν := ⟨hw ℚ le_rfl ν, hwMem ℚ _ _ le_rfl ν hν⟩
  let φ : dualWeyl ℚ (p + q) (p + q) ν →ₗ[ℚ] ℚ :=
    { toFun := fun x => fockQ (hw ℚ le_rfl ν) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
      map_add' := fun x y => LR.fock_add_right _ _ _
      map_smul' := fun c x => LR.fock_smul_right _ _ _ }
  have hwz : ∀ c : Fin (p + q), wtZ ν c = ν c := fun c => by simp [wtZ]
  have hv : IsWt (p + q) e (wtZ ν) v := by
    intro c hc
    apply Subtype.ext
    have h1 := eV_coe ν ⟨c, hc⟩ ⟨c, hc⟩ v
    have h2 := (LR.der_diag_iff _ _).1 (LR.hw_rowHom ν hν) ⟨c, hc⟩
    have h3 := hwz ⟨c, hc⟩
    simp only at h1 h3
    rw [he, h1, h3]
    simpa using h2
  have hsc := hS _ p q K e (wtZ ν) v φ T hrel hdom hv (fun i j hij hj => by
    have hi : i < p + q := hij.trans hj
    have hr := LR.der_hw_raise ν ⟨i, hi⟩ ⟨j, hj⟩ hij
    have h3 := hwz ⟨i, hi⟩
    have h4 := hwz ⟨j, hj⟩
    simp only at h3 h4
    refine ⟨Subtype.ext ?_, fun x => ?_, ?_, ?_⟩
    · exact (eV_coe ν ⟨i, hi⟩ ⟨j, hj⟩ v).trans hr
    · have h1 := eV_coe ν ⟨j, hj⟩ ⟨i, hi⟩ x
      change fockQ _ (eV (p + q) ν j i x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
      simp only at h1
      rw [h1, ← LR.fock_der, hr]
      simpa using LR.fock_smul_left (0 : ℚ) 0 (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ)
    · rw [h3, h4]; exact_mod_cast hν (show (⟨i, hi⟩ : Fin (p + q)) ≤ ⟨j, hj⟩ from hij.le)
    · rw [h3, h4]; exact_mod_cast hK _ _) hT3
  set z : ℤ := ∏ i ∈ Finset.range p, ∏ j ∈ Finset.Ico p (p + q), (wtZ ν i - wtZ ν j + (j : ℤ) - (i : ℤ)) with hz
  have hone : (z : ℚ) • S₀ = 1 := by
    refine hSch (p + q) ν hν _ (fun c hc d hd => ?_) ?_
    · have := hinv c hc d hd
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero] at this
      rw [mul_smul_comm, smul_mul_assoc, ← he, this]
    · change φ (((z : ℚ) • S₀) v) = _
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_comm, hsc]
      exact hT4
  intro x hx
  let x' : dualWeyl ℚ (p + q) (p + q) ν := ⟨intQ _ _ x, (dualWeylIntRat _ _ ν x).1 hx⟩
  have hx' : x' ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν) := ⟨x, hx, rfl⟩
  have h5 := Submodule.smul_mem _ z (hI _ p q K w Λ e _ _ hst1 hst2 hw' hΛ (c₁ * c₂) T hT2 x' hx')
  rw [smul_comm, ← hS₀] at h5
  have h6 : z • S₀ x' = x' := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← LinearMap.smul_apply, hone]; rfl
  rw [h6] at h5
  obtain ⟨y, hy, hyx⟩ := h5
  have h7 : y = ((c₁ * c₂ * Λ ^ (p * q) : ℕ) : ℤ) • x := by
    apply map_injective (Int.castRingHom ℚ) (fun a b h => by simpa using h)
    change intQ _ _ y = intQ _ _ _
    rw [hyx, map_smul, map_smul]
    rfl
  exact h7 ▸ hy

theorem ExCut₂ (hG : GridInv) (hA : AdjBdd) (hS : GridScalar) (hI : GridInt) (hN : NablaGl) (hB : NablaBdd)
    (hSch : NablaSchur) (hL : LeviProj) (hD : BetaDen) : Formalism.CohomologicalDescent.E.ExCut := by
  intro N lam hlam l hl lo w hU a ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hcast : ∀ c, c = b → exZ c c le_rfl (LD.res c (fun i => lam (a + i))) l =
      exZ b b le_rfl (LD.res b (fun i => lam (a + i))) l := by rintro c rfl; rfl
  rw [hcast (a + b - a) (by omega), Nat.add_sub_cancel_left]
  have hA1 : Antitone (LD.res a lam) := fun i j hij =>
    hlam (show (Fin.castAdd b i) ≤ Fin.castAdd b j from hij)
  have hA2 : Antitone (LD.res b (fun i => lam (a + i))) := fun i j hij =>
    hlam (show (Fin.natAdd a i) ≤ Fin.natAdd a j by rw [Fin.le_def] at hij ⊢; simpa using hij)
  obtain ⟨m₁, hm₁, h₁⟩ := exact_z_specialization a a le_rfl _ hA1 l hl
  obtain ⟨m₂, hm₂, h₂⟩ := exact_z_specialization b b le_rfl _ hA2 l hl
  obtain ⟨m, hm, hden⟩ := hD l w hl
  have hsp : ∀ i j : Fin (a + b), i ≤ j → lam i + j ≤ lam j + w + i := fun i j _ => by
    have h1 := (hU i i.2).2
    have h2 := (hU j j.2).1
    simp only [UnitNormBounds.UN] at h1 h2
    omega
  have hK : ∀ i j : Fin (a + b), LD.res (a + b) lam i ≤ LD.res (a + b) lam j + (w + 1 - (a + b)) := fun i j => by
    have hpos : 0 < a + b := lt_of_le_of_lt (Nat.zero_le _) i.2
    have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
    have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ i by simp [Fin.le_def])
    have h3 := hlam (show j ≤ (⟨a + b - 1, by omega⟩ : Fin (a + b)) by rw [Fin.le_def]; have := j.2; simp only; omega)
    simp only [LD.res] at h1 h2 h3 ⊢
    omega
  have hw' : (w + 1 - (a + b)) + (a + b) ≤ w + 1 := by
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · omega
    · have h1 := hsp ⟨0, hpos⟩ ⟨a + b - 1, by omega⟩ (by simp [Fin.le_def])
      have h2 := hlam (show (⟨0, hpos⟩ : Fin (a + b)) ≤ ⟨a + b - 1, by omega⟩ by simp [Fin.le_def])
      simp only [LD.res] at h1 h2
      omega
  have key := cut_incl hG hA hS hI hN hB hSch hL a b (LD.res (a + b) lam) hlam _ _ _ w _ h₁ h₂ hK hw' hden
  refine Nat.sInf_le ⟨m₁ * m₂ * m ^ (a * b), ?_, fun x hx => ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
      · exact hm₁ h
      · exact hm₂ h
    · exact hm (hl.dvd_of_dvd_pow h)
  · convert key x hx using 3
    rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm (Nat.log l w)]
    ring

theorem exCut : Formalism.CohomologicalDescent.E.ExCut :=
  ExCut₂ (GlobalTheory.T.grid_invariance_of_rank_one_two _root_.GlobalTheory.LeviCut.rankOne _root_.GlobalTheory.LeviCut.RankTwoProof.rankTwo) _root_.GlobalTheory.LeviCut.adjBdd_holds (_root_.GlobalTheory.LeviCut.gridScalar_of_stepScalar _root_.GlobalTheory.LeviCut.StepScalarProof.stepScalar) _root_.GlobalTheory.LeviCut.gridInt_holds
    _root_.GlobalTheory.LeviCut.nablaGl _root_.GlobalTheory.LeviCut.nablaBdd _root_.GlobalTheory.LeviCut.nablaSchur
    (_root_.GlobalTheory.LeviCut.leviProj_of (_root_.GlobalTheory.LeviCut.resLat_of_substMem _root_.GlobalTheory.LeviCut.substMem) _root_.GlobalTheory.LeviCut.resHw_holds _root_.GlobalTheory.LeviCut.dualWeyl_resDer) _root_.GlobalTheory.LeviCut.betaDen

end GlobalTheory.LeviCut
end
end

