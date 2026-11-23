module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyZeroOfDeRhamCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqOfMemDpcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersSubsetTameType
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.CharsDesc

theorem toBcris_inj {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (hB : Function.Injective (ϖ.iB t K)) :
    Function.Injective (toBcris t ϖ P) := by
  intro m m' h
  have hc : coordL P (invL l (S O K e)) m = coordL P (invL l (S O K e)) m' := by
    funext i
    apply hB
    have := congrFun h i
    rwa [toBcris_apply, toBcris_apply] at this
  apply Subtype.ext
  funext τ
  rw [← mx_mulVec_coordL P _ m τ, ← mx_mulVec_coordL P _ m' τ, hc]

theorem xi_mem_MMl {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (d : P.D) :
    P.xi d ∈ P.MMl := by
  refine ((_root_.GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 (cst d)).2 ?_
  refine mem_tot.2 fun τ i => ?_
  obtain ⟨n, b, hb⟩ := exists_pow_mul_mem (O := O) l (d τ i)
  refine ⟨n, ?_⟩
  have h1 : (((l : S O K e) : K⟦X⟧)) ^ n * cst d τ i = algebraMap O K⟦X⟧ b := by
    rw [IsScalarTower.algebraMap_apply O K K⟦X⟧, ← hb]
    simp [cst, PowerSeries.algebraMap_apply]
  rw [h1]
  exact Subalgebra.algebraMap_mem _ b

theorem actD_single {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {P : PhiMod O K l e a ι} (Δ : Descent P)
    (ζ : rootsOfUnity e K) (d : P.D) (τ : ZMod a) :
    Δ.actD (TameGal.inertia ζ) (Pi.single τ (d τ) : P.D) = Pi.single τ (Δ.actD (TameGal.inertia ζ) d τ) := by
  classical
  have hf : ringAct (TameGal.inertia ζ : TameGal K l e a) (Pi.single τ 1) = Pi.single τ 1 := by
    funext σ
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero]
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have hc : cst (Pi.single τ (d τ) : P.D) = (Pi.single τ 1 : ZMod a → K⟦X⟧) • cst d := by
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [cst]
    · simp [cst, h]
  have hr : ∀ w : Vec K a ι, red ((Pi.single τ 1 : ZMod a → K⟦X⟧) • w) = Pi.single τ (red w τ) := by
    intro w
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [red, red0]
    · simp [red, red0, h]
  change red (Δ.act _ (cst _)) = _
  rw [hc, Δ.act_smul_tot, hf, hr]
  rfl

theorem jB_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {ι : Type} [Fintype ι]
    (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (o : ↥(OL LL))
    (v : ι → OB l ↥(OL LL)) : jB (o • v) = o • jB v := by
  haveI : IsScalarTower ↥(OL LL) (OB l ↥(OL LL)) (TW (OB l ↥(OL LL)) T) :=
    TensorProduct.isScalarTower_left (R := ↥(OL LL)) (M := OB l ↥(OL LL)) (N := ↥T.L.T)
      (R' := OB l ↥(OL LL)) (R'₂ := ↥(OL LL))
  rw [← algebraMap_smul (OB l ↥(OL LL)) o v, map_smul, algebraMap_smul]

theorem smul_eq_algebraMap_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (o : ↥(OL LL)) (x : T.V ⊗[ℚ_[l]] Pl.R.B) : o • x = (algebraMap ↥(OL LL) ↥LL.1 o) • x :=
  (algebraMap_smul (↥LL.1) o x).symm

theorem mem_Dcris_res {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l) (F : FinExt l)
    (x : (resF T F).V ⊗[ℚ_[l]] Pl.R.B)
    (h : ∀ g : ↥(GK F), actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) (x : T.V ⊗[ℚ_[l]] Pl.R.B) = x) :
    x ∈ Dcris (Pl.PD F) (resF T F).ρ := by
  refine (Submodule.mem_iInf _).2 fun g => LinearMap.mem_ker.2 (sub_eq_zero.2 ?_)
  have key : actVB (Pl.PD F) (resF T F).ρ g = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) := by
    unfold actVB
    congr 1
    ext b
    exact (Pl.PD_actB F g b).trans (Pl.PD_actB _ (inclG F g) b).symm
  exact (LinearMap.congr_fun key x).trans (h g)

end GlobalTheory.CharsDesc


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
open GlobalTheory.CharsDesc in
theorem GlobalTheory.CharsDesc.chars_subset_sig : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Δ : Descent P) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → IsGalDesc (sQ l) I Δ → ∀ Sig : Finset (ZMod e), TameType a ϖ Pl T Sig → ∀ τ, Δ.chars τ ⊆ (Sig : Set (ZMod e)) := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Δ Pl AI hStd hCmp hHor hDesc Sig hType τ c hc
  have hpoly : ∀ (z : ↥LL.1) (n : ℕ),
      (∏ j ∈ Sig, (Polynomial.X - Polynomial.C (z ^ j.val)) : Polynomial ↥LL.1).eval (z ^ n) = 0 →
      ∃ j ∈ Sig, z ^ n = z ^ j.val := by
    intro z n h
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff, sub_eq_zero] at h
    exact h
  have hc0 : c ∈ Δ.chars 0 := by
    rw [← (GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable _ _ l e a ι P Δ).1 τ 0]; exact hc
  obtain ⟨d, hd0, hdc⟩ := hc0

  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  obtain ⟨ζu, hζu⟩ : ∃ ζu : rootsOfUnity e ↥LL.1, (((ζu : (↥LL.1)ˣ) : ↥LL.1)) = ζ := ⟨hζ.toRootsOfUnity, rfl⟩
  have I8 := _root_.GlobalTheory.TameCover.main l a e ϖ LL
  obtain ⟨k, -, hkc⟩ := I8.2.2.1 (TameGal.inertia ζu)
  obtain ⟨k', hk'I, hk'c, hk'π⟩ := I8.2.2.2.2.2.2 k ζu hkc
  classical
  obtain ⟨d', hd'_def⟩ : ∃ d' : P.D, d' = Pi.single 0 (d 0) := ⟨_, rfl⟩
  have hd'0 : d' ≠ 0 := by
    intro h; apply hd0; have := congrFun h 0; rw [hd'_def, Pi.single_eq_same] at this; exact this
  have hact' : Δ.actD (TameGal.inertia ζu) d' = (ζ ^ c.val) • d' := by
    rw [hd'_def, actD_single, hdc ζu, TameGal.root_inertia_zero, hζu, Pi.single_smul]
  have hm := xi_mem_MMl P d'
  obtain ⟨σ, hσ_def⟩ : ∃ σ : P.MMl, σ = ⟨P.xi d', hm⟩ := ⟨_, rfl⟩
  have hnorm : ‖ζ ^ c.val‖ ≤ 1 := by
    have h1 : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h
    rw [norm_pow, h1, one_pow]
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := ↥(OL LL)) (ζ ^ c.val)).2 hnorm
  have hσ' : (o • σ).1 = Δ.act (TameGal.inertia ζu) σ.1 := by
    rw [hσ_def, Descent.act_xi, hact', map_smul, Submodule.coe_smul_of_tower, ← ho, algebraMap_smul]
  have hA := _root_.GlobalTheory.TameAct.main l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I jB Δ hCmp hDesc k'
    (TameGal.inertia ζu) hk'c σ (o • σ) hσ'
  obtain ⟨β, -, hβ2, -, -⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hStd
  obtain ⟨x, hx_def⟩ : ∃ x, x = β (jB (toBcris (thetaW a LL) ϖ P σ)) := ⟨_, rfl⟩
  have hx0 : x ≠ 0 := by
    intro h
    rw [hx_def, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h
    have h2 : σ = 0 := toBcris_inj (thetaW a LL) ϖ P (_root_.GlobalTheory.BKReal.IBInj.iB_injective_finExt l a e LL (thetaW a LL) ϖ)
      (h.trans (map_zero _).symm)
    apply hd'0
    have h3 : P.xi d' = 0 := by rw [hσ_def] at h2; exact congrArg Subtype.val h2
    have h4 := congrArg red h3
    rwa [PhiMod.red_xi, map_zero] at h4
  have hxD : x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ := by
    refine mem_Dcris_res T Pl (ϖ.field a) x fun g => ?_
    have e := hβ2 (inclG (ϖ.field a) g) (jB (toBcris (thetaW a LL) ϖ P σ))
    have e' : actB (sQ l) T (inclG (ϖ.field a) g) (jB (toBcris (thetaW a LL) ϖ P σ)) =
        jB (toBcris (thetaW a LL) ϖ P σ) := by
      subst hσ_def; exact hHor (inclG (ϖ.field a) g) g.2 d' hm
    rw [e'] at e
    subst hx_def; exact e.symm
  have hA' : actB (sQ l) T k' (jB (toBcris (thetaW a LL) ϖ P σ)) =
      jB (toBcris (thetaW a LL) ϖ P (o • σ)) := hA
  have hact : (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) x =
      (ζ ^ c.val) • x := by
    have e1 := (hβ2 k' (jB (toBcris (thetaW a LL) ϖ P σ))).symm
    have e6 := congrArg β hA'
    have e2 : toBcris (thetaW a LL) ϖ P (o • σ) = o • toBcris (thetaW a LL) ϖ P σ := map_smul _ _ _
    have e3 : jB (o • toBcris (thetaW a LL) ϖ P σ) = o • jB (toBcris (thetaW a LL) ϖ P σ) :=
      jB_smul jB o _
    have e4 : β (jB (toBcris (thetaW a LL) ϖ P (o • σ))) = o • β (jB (toBcris (thetaW a LL) ϖ P σ)) :=
      (congrArg (fun v => β (jB v)) e2).trans ((congrArg β e3).trans (β.map_smul o _))
    subst hx_def
    refine e1.trans (e6.trans (e4.trans ?_))
    exact (smul_eq_algebraMap_smul T Pl o _).trans
      (congrArg (fun s : ↥LL.1 => s • β (jB (toBcris (thetaW a LL) ϖ P σ))) ho)
  have hk'π' : ((ζ : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by rw [← hζu]; exact hk'π
  have hT := hType k' hk'I ζ hk'π' x hxD
  have hev : Module.End.HasEigenvector
      (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) (ζ ^ c.val) x :=
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hact, hx0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev, smul_eq_zero] at hT
  rcases hT with hT | hT
  · obtain ⟨c', hc', hcc⟩ := hpoly ζ c.val hT
    have := hζ.pow_inj (ZMod.val_lt c) (ZMod.val_lt c') hcc
    rw [ZMod.val_injective e this]
    exact hc'
  · exact absurd hT hx0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_type_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e)), (0 : ZMod e) ∈ Sig → TameType a ϖ Pl T Sig → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  first | exact @GlobalTheory.TameExt.tameType_extLat | exact GlobalTheory.TameExt.tameType_extLat | (intros; apply GlobalTheory.TameExt.tameType_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

namespace GlobalTheory.PotDirect

theorem main : StepPotDirect := by
  intro D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw
  obtain ⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩ := GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw
  have hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simpa [chiGL, Matrix.scalar] using D.nd.chi_cont i 1
  obtain ⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩ := GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV
    (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ
  obtain ⟨ch, hch⟩ := GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker
  have hdeg := (GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw
  refine _root_.GlobalTheory.PotTwist.main D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1)
    (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_
  · intro x hx
    obtain ⟨M, hM, hσ⟩ := (hX x hx).2
    exact ⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩
  · have := hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)
    simpa using this

end GlobalTheory.PotDirect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
section
noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem IsIso.stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem IsIso.kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem IsIso.identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [h₁.kapSum_eq h₂, h₁.stSum_eq, h₂.stSum_eq, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (cut B e he).A +
      Module.finrank K.E (cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (cut B e he).P * (cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  rcases subsingleton_or_nontrivial B.A with hs | hs
  · exact Or.inl ⟨0, zero_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hid : ∀ e : Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → e = 0 ∨ e = 1
  · have : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
      Module.Finite.iff_fg.2 hi.fg_adjoin_singleton
    exact Or.inr (isLocalRing_of_idem (R := K.O) _ hid)
  push Not at hid
  obtain ⟨⟨e, he⟩, hee, h0, h1⟩ := hid
  have hee : e * e = e := congrArg Subtype.val hee
  have h0 : e ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : e ≠ 1 := fun h => h1 (Subtype.ext h)
  have he' := adjoin_stable B hu hi he
  have hee' : B.σ e * B.σ e = B.σ e := by rw [← map_mul, hee]
  have hm : e * B.σ e = 0 := by
    refine (h _ (mul_mem he he') ?_ ?_).resolve_right fun h2 => h1 ?_
    · linear_combination B.σ e * B.σ e * hee + e * hee'
    · rw [map_mul, B.σ_σ, mul_comm]
    · linear_combination (1 - e) * h2 + B.σ e * hee
  refine Or.inl ⟨e, he, hee, (h _ (add_mem he he') ?_ ?_).resolve_left fun h2 => h0 ?_⟩
  · linear_combination hee + hee' + 2 * hm
  · rw [map_add (f := _), B.σ_σ, add_comm]
  · linear_combination e * h2 - hee - hm

theorem identity_integral (hL : UnitLemmaLie) (hK : K.Odd) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact _root_.GlobalTheory.UnitLemma.Swap.identity_of_swap K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact _root_.GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie hL K hK B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (cut B₁ e₁ s₁).A + Module.finrank K.E (cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine (isIso_cut B₁ j₁ s₁).identity (isIso_cut B₂ j₂ s₂) ?_
  refine _root_.GlobalTheory.UnitLemma.ProdId.identity_prod K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem unitLemmaGroup_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  intro hL K hK B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL hK _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.Orbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStableStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_invQPow_gamma_stable : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  first | exact @GlobalTheory.NL.GamQ.gam_Q_pow | exact GlobalTheory.NL.GamQ.gam_Q_pow | (intros; apply GlobalTheory.NL.GamQ.gam_Q_pow <;> assumption)
end

