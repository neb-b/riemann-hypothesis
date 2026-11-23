module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpAct
open GlobalTheory.UT GlobalTheory.ThetaScalar

variable {R : Type} [CommRing R] [IsDomain R] {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E]
  [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem exists_frame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : w.IsGen) :
    ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J := by
  obtain ⟨hy, hb, hs⟩ := h
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F p'.g.b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem txFrame_pull {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} (hw : TXFrame k p w) {w' : Frm D F k p'.g.b} (hw' : w'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) : TXFrame k p' w' := by
  obtain ⟨hy, hb, hs⟩ := h
  have hL := D.P.isLB
  have hb' : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ p.g.b.left = p'.g.b.left := by
    rw [Category.id_comp]; exact hb.symm
  refine ⟨hw', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
  · have c : LB.Gen.Corr D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w 2)
        (LB.mulGen D.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.P.L _ _ ν p.g.b.left)) :=
      corr_of_val hL fun y I hI => (map_pow _ _ _).trans ((hw.2.1 ν hν y I hI).trans (by
        rw [val_mul hI, val_pull hI, Category.id_comp]))
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    rw [val_mul hJ, val_pull hJ, hb'] at e
    rw [hv _ _ z J hJ, val_corr hJ (hs p'.y), val_pull hJ, hy]
    exact (map_pow _ _ _).symm.trans e
  · have c : LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ w k) (LB.pullGen D.P.L _ _ κ p.g.b.left))
        (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi p.y) (jFK (R := R) E))
          (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (TF (R := R) E).hom)) :=
      corr_of_val hL fun y I hI => by
        rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, val_pull hI, Category.id_comp, Category.id_comp,
          Category.id_comp]
        exact (congrArg (· * _) (map_pow _ _ _)).trans (hw.2.2 κ hκ y I hI)
    have e := val_corr hJ c (𝟙 _ ≫ (baseMap (R := R) E F).left)
    have e₁ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ jFK (R := R) E = jFK (R := R) F := by
      rw [Category.id_comp]; exact specMap_jFK E F
    have e₂ : (𝟙 _ ≫ (baseMap (R := R) E F).left) ≫ (TF (R := R) E).hom = (TF (R := R) F).hom := by
      rw [Category.id_comp]; exact Over.w _
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb', e₁, e₂] at e
    rw [hv _ _ z J hJ, hy]
    exact (congrArg (· * _) (map_pow _ _ _)).symm.trans e

theorem phiVal_pull (hG : GlobalFnsSt) {D : DegPre R} {k : ℕ} {p : QkPt D E k} {p' : QkPt D F k}
    (h : QkExt (algebraMap E F) p p') {w : Frm D E k p.g.b} {w' : Frm D F k p'.g.b}
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val w' r z J = val w (r ≫ (baseMap (R := R) E F).left) z J) (s t : Fam D E k) (H : PhiVal p w s.s t.s) :
    PhiVal p' w' (famPull D E F hG k s).s (famPull D E F hG k t).s := by
  obtain ⟨hy, hb, hs⟩ := h
  have hb' : p'.g.b = baseMap (R := R) E F ≫ p.g.b := Over.OverMorphism.ext hb
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D F p'.g.b ≫ famMap D E F = famMap D E F ≫ DegPre.trPt D E p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D E F)).trans (tr_pr D F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D E _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D E F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) E F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D E k α p.g.b (ρ ≫ famMap D E F) z J = uVal D F k α p'.g.b ρ z J := by
    have : famMap D E F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D E F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, hv _ _ z J hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

theorem secMap_eq (A : PolAV (Sp (FractionRing R))) : secMap A E F = baseK (R := R) E F ▷ A.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [secMap_fst, whiskerRight_fst]
  · rw [secMap_snd, whiskerRight_snd]

theorem actVal_secPull {A : PolAV (Sp (FractionRing R))} {N : ℕ} (hN : Odd N) {x : TFK (R := R) E ⟶ A.A}
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) E)} {θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)}
    (H : SymLift A.A A.L N N x θ) (H' : SymLift A.A A.L N N (baseK (R := R) E F ≫ x) θ')
    {t u : SecF A E N} (h : ActVal θ t u) : ActVal θ' (UpExt.secPull A E F N t) (UpExt.secPull A E F N u) := by
  obtain ⟨ξ, Hξ, v⟩ := SymLiftGlobal.exists_symLift_pull_val A.isLB (baseK (R := R) E F) H
  have c := SymLiftOdd.symLift_unique GlobalTheory.globalFns_holds A.isAb A.isLB hN θ' ξ H' Hξ
  intro Z r z J hJ
  have h₂ : thetaVal θ' r z J = thetaVal θ (r ≫ (secMap A E F).left) z J := by
    rw [secMap_eq]; exact (val_corr hJ c _).trans (v _ _ z J hJ)
  refine (sval_pullOver _ _ _ _ hJ).trans ((h _ _ z J hJ).trans (congrArg₂ (· * ·)
    (congrArg Units.val h₂.symm) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm)))
  have e : (translT A.A θ'.pt).left ≫ (secMap A E F).left = (secMap A E F).left ≫ (translT A.A θ.pt).left := by
    rw [H'.pt_eq, H.pt_eq, secMap_eq]
    exact congrArg (fun q => q.left) (CommPairing.whisker_translT (baseK (R := R) E F) x)
  rw [Category.assoc, Category.assoc, e]
  rfl

end GlobalTheory.Mum.UpAct


open GlobalTheory.Mum.UpAct GlobalTheory.UT GlobalTheory.ThetaScalar in
theorem GlobalTheory.Mum.UpAct.act_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) (E₀ : Fam D.toPre (Kb R) N → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), Eqv D.toPre A (Kb R) N lab E₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (Kb R) F] [IsScalarTower (FractionRing R) (Kb R) F] (lab' : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A)), LabExt (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) lab lab' → ∀ (E' : Fam D.toPre F N →ₗ[F] SecF A F N), (∀ s, E' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s) = UpExt.secPull A (Kb R) F N (E₀ s)) → ∀ (p : QkPt D.toPre F N) w (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (s s' : Fam D.toPre F N), GlobalTheory.UT.TXFrame N p w → SymLift A.A A.L N N (lab' p) θ → PhiRel D.toPre F N p w s s' → IsActOf A.A A.L N θ (E' s) (E' s') := by
  intro R _ _ _ hR D A N hN lab E₀ hE F _ _ _ _ _ lab' hlab E' hE' p w θ s s' hw hθ hs
  have : CharZero R := hR.2
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨p₀, hp, -⟩ := (qkPt_algClosure_bijective R D.toPre F
    (IsScalarTower.toAlgHom (FractionRing R) (Kb R) F) N hN.pos).2 p
  have hx : lab' p = baseK (R := R) (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp)
  replace hp : QkExt (algebraMap (Kb R) F) p₀ p := hp
  obtain ⟨w₀, hw₀⟩ := hE.frame p₀
  obtain ⟨θ₀, hθ₀⟩ := hE.lift p₀
  obtain ⟨w', hw', hv'⟩ := exists_frame_pull hp hw₀.1
  have hu := (GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R _ hR.1 D F N hN p).2 w w' hw (txFrame_pull hp hw₀ hw' hv')
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.toPre.P.L z J →
      val w r z J = val w₀ (r ≫ (baseMap (R := R) (Kb R) F).left) z J := fun Z r z J hJ =>
    (val_corr hJ (corr_of_val D.toPre.P.isLB hu) r).trans (hv' Z r z J hJ)
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of_globalFns hG R _ D (Kb R) N hN.pos p₀ w₀ hw₀.1
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG R _ D F N hN.pos p w hw.1
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : SecF A F N →ₗ[F] SecF A F N, ∀ t, ActVal θ t (Θ t) := GlobalTheory.TorsionExt.exists_act θ
  rw [hx] at hθ
  have key : E' ∘ₗ Φ = Θ ∘ₗ E' := LinearMap.ext_on
    (isExtension_famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds hN.pos).span (by
      rintro _ ⟨u, rfl⟩
      have r₀ : PhiRel D.toPre (Kb R) N p₀ w₀ u (Φ₀ u) := (hΦ₀ u _).2 rfl
      have r := (hΦ _ _).1 ((phiRel_iff hG p w hw.1 _ _).2
        (phiVal_pull GlobalTheory.globalFns_holds hp hv u _ ((phiRel_iff hG p₀ w₀ hw₀.1 _ _).1 r₀)))
      have a := actVal_secPull hN hθ₀ hθ (ThetaBaseChange.actVal_of_isActOf (hE.act p₀ w₀ θ₀ u _ hw₀ hθ₀ r₀))
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← r, hE', hE']
      exact GlobalTheory.TorsionExt.actVal_unique a (hΘ _))
  obtain rfl := (hΦ _ _).1 hs
  have e : E' (Φ s) = Θ (E' s) := LinearMap.congr_fun key s
  rw [e]
  exact (hΘ _).isActOf A.isLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R := by
  refine { toIsCoideal := { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_ },
           antipode_mem := ?_ }
  · intro x hx
    have hle : kerIdeal f ≤ augIdeal R A := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [CoalgHomClass.counit_comp_apply] using hc'
    simpa using hle hx
  · intro x hx
    let Q := A ⧸ kerIdeal f
    let q := Ideal.Quotient.mkₐ R (kerIdeal f)
    let Φ : A →ₐ[R] Q ⊗[R] Q := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A)
    have hqf : ∀ c : C, q (f c) = algebraMap R Q (counit (R := R) c) := by
      intro c
      have hmem : f (c - algebraMap R C (counit (R := R) c)) ∈ kerIdeal f := by
        refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : q (f (c - algebraMap R C (counit (R := R) c))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0
    have hg : q.toLinearMap ∘ₗ (f : C →ₗ[R] A) = Algebra.linearMap R Q ∘ₗ counit :=
      LinearMap.ext hqf
    have hΦ : kerIdeal f ≤ RingHom.ker Φ := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
      rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
        hg]
      have hsplit : TensorProduct.map (Algebra.linearMap R Q ∘ₗ counit)
          (Algebra.linearMap R Q ∘ₗ counit) =
          TensorProduct.map (Algebra.linearMap R Q) (Algebra.linearMap R Q ∘ₗ counit) ∘ₗ
            LinearMap.rTensor C (counit (R := R) (A := C)) := by
        rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
      rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
      simp [hc']
    exact hΦ hx
  · have h0 : ((1 : WithConv (A →ₐ[R] A)).ofConv).comp (f : C →ₐ[R] A) =
        (1 : WithConv (C →ₐ[R] A)).ofConv := by
      ext c
      simp [CoalgHomClass.counit_comp_apply]
    have h1 : WithConv.toConv ((HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A)) *
        WithConv.toConv (f : C →ₐ[R] A) = 1 := by
      have := AlgHom.convMul_comp_bialgHom_distrib
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom R A)) (WithConv.toConv (AlgHom.id R A)) f
      rw [AlgHom.antipode_id_cancel, h0] at this
      apply WithConv.ofConv_injective
      rw [this]
      rfl
    have h2 : (HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A) =
        (f : C →ₐ[R] A).comp (HopfAlgebra.antipodeAlgHom R C) :=
      congrArg WithConv.ofConv (eq_inv_of_mul_eq_one_left h1)
    have hS : ∀ c : C, HopfAlgebra.antipode R (f c) = f (HopfAlgebra.antipode R c) := fun c => by
      simpa using DFunLike.congr_fun h2 c
    have hle : kerIdeal f ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom R A) (kerIdeal f) := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hc' : counit (R := R) c = 0 := by simpa using hc
      change HopfAlgebra.antipode R (f c) ∈ kerIdeal f
      rw [hS]
      refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
      rw [RingHom.mem_ker]
      simpa using hc'
    intro x hx
    exact hle hx

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((verschiebung h G).app 1) w' := by
    have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    let V := (verschiebung h G).app 1
    let F := (relFrob h G).app 1
    let J : Ideal ((frobTwist h G).A 1) := kerIdeal V
    have : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπker : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker K J
    have : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    have : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) :=
      (kerIdeal_le_ker_iff V (AlgHom.ofClass π)).mp hπker.ge

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply pow_char_eq_zero_of_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ :=
      exists_primitive_dUnit_eq p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      rw [hπker]
      exact app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K (frobTwist h G) G
        (verschiebung h G) (relFrob h G) (relFrob_comp_verschiebung h G)
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    obtain ⟨w', hw'⟩ := (exact_cotMap hπ V hπker (dUnit (R := K) β - w)).mp (by
      rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam.AdicSum

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_finsum {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (β : D.X) (T : Finset Ix) (hT : ∀ i ∈ T, w i = β) :
    ∃ g : SecT D a n j β, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval g r z J = ∑ i ∈ T, sval (s i) r z J := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨zeroT D a n j β, fun Z r z J hJ => by rw [sval_zeroT _ _ _ _ _ _ z J hJ, Finset.sum_empty]⟩
  | insert i T hi ih =>
    obtain ⟨g, hg⟩ := ih fun k hk => hT k (Finset.mem_insert_of_mem hk)
    obtain rfl := hT i (Finset.mem_insert_self _ _)
    refine ⟨H1.SectionArithmetic.secAdd (s i) g, fun Z r z J hJ => ?_⟩
    rw [Finset.sum_insert hi, ← hg Z r z J hJ]
    exact gs_add r z _ (hJ.mem _ r) _ _


open Classical in
theorem sum_indep (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (e : ℕ) (S S' : Finset Ix) (hS : ∀ i ∉ S, Van I (s i) e)
    (hS' : ∀ i ∉ S', Van I (s i) e) (δ : D.X) {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J)
    (hJ : Good D.P.L z J) :
    ∑ i ∈ S.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
      ∑ i ∈ S'.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J := by
  have key : ∀ T T' : Finset Ix, (∀ i ∉ T, Van I (s i) e) → T ⊆ T' →
      ∑ i ∈ T.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
      ∑ i ∈ T'.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J :=
    fun T T' hT h => Finset.sum_subset (Finset.filter_subset_filter _ h) fun i hi hi' =>
      hT i (fun hm => hi' (Finset.mem_filter.2 ⟨hm, (Finset.mem_filter.1 hi).2⟩)) Z x z J hJ
  exact (key S (S ∪ S') hS Finset.subset_union_left).trans (key S' (S ∪ S') hS' Finset.subset_union_right).symm

omit [IsDomain R] in
theorem thickMap_fst (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem van_of_succ (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) (h : Van I s (e + 1)) : Van I s e := fun Z x z J hJ => by
  have := h Z (x ≫ thickMap R I e D.P.A) z J hJ
  rwa [Category.assoc, thickMap_fst] at this

theorem exists_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ F : ∀ β, SecT D.toPre a n j β, IsSum (maximalIdeal R) s F ∧ Small (maximalIdeal R) (w := id) F := by
  intro R _ _ _ hR D a n j Ix w s hs
  classical
  have hC := hR.2.2.2
  have hS : ∀ e, ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun e i hi => by
    by_contra h
    exact hi ((Set.Finite.mem_toFinset _).2 h)
  choose g hg using fun e β => exists_finsum s β ((hs e).toFinset.filter (fun i => w i = β))
    (fun i hi => (Finset.mem_filter.1 hi).2)
  choose F hF using fun β => GlobalTheory.SecAlgLinComb.exists_sec_linComb R (maximalIdeal R) hC D.toPre.P.A
    D.toPre.P.isAb.smooth (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L (Fin 5)
    (tφ D.toPre a β) (tε n j) _ D.toPre.P.isLB (fun _ _ => rfl)
    (fun e => H1.SectionArithmetic.pullSec (g e β) (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun e z J hJ => by
      refine (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans (Eq.trans ?_ (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).symm)
      rw [thickMap_fst, hg _ _ _ _ z J hJ, hg _ _ _ _ z J hJ]
      refine Eq.trans ?_ (sum_indep (maximalIdeal R) s e _ _ (fun i hi => van_of_succ _ _ e (hS (e + 1) i hi)) (hS e) β
        (𝟙 _) z J hJ)
      rw [Category.id_comp])
  have hsum : IsSum (maximalIdeal R) s F := fun e S hS' δ Z x z J hJ => by
    refine (hF δ e Z x z J hJ).trans ((H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans ((hg _ _ _ _ z J hJ).trans ?_))
    convert sum_indep (maximalIdeal R) s e _ _ (hS e) hS' δ x z J hJ
  refine ⟨F, hsum, fun e => ((hs e).image w).subset fun β hβ => ?_⟩
  by_contra hn
  refine hβ fun Z x z J hJ => (hsum e _ (hS e) β Z x z J hJ).trans (Finset.sum_eq_zero fun i hi => ?_)
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 hi
  exact (hn ⟨i, (Set.Finite.mem_toFinset _).1 h₁, h₂⟩).elim

end GlobalTheory.TwFam.AdicSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem q_comm_of_coordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) (hF : IsCoordEnd g a a' h' u F) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have h2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ a.left := by
      simp
    rw [h2]
    exact hF.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have w1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w g.q
    have w2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.snd D.P.A.hom (thick R I e) =
        pullback.snd D.P.A.hom (thick R I e) := Over.w ((Over.pullback (thick R I e)).map a)
    have w3 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [w2, w1]
    exact w3

theorem formalEnd_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hE
  obtain ⟨ha, ha', hr, -, hc, -⟩ := hE
  have hr' := GlobalTheory.Mum.RosatiSymmetry.rosatiAdj_symm D.toPre.P.A D.toPre.P.L D.toPre.P.isLB a a' hr
  obtain ⟨u, hu, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB a' a hr'
  choose F hF using fun e => GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀
  exact ⟨F, fun e => _root_.GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd (U.gt e) a a' h' hc u hu h₀ (F e) (hF e),
    fun e => _root_.GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat U.toUnifPre e a a' h' u (F e) (F (e + 1)) (hF e) (hF (e + 1)),
    fun e => q_comm_of_coordEnd (U.gt e) a a' h' u (F e) (hF e),
    fun e => _root_.GlobalTheory.Mum.EndThick.torus_of_isCoordEnd (U.gt e) a a' h' u hu h₀ (F e) (hF e)⟩

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellPointBasicOpenAffineSpaceCoordsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bigCell_point_basicOpen_affineSpace_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), Nonempty W → ∃ g : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1), ¬ IsNilpotent (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g) ∧ (∀ (S : Type) [CommRing S] (z₀ : Sp S ⟶ Y₀ TF.X Z) (hz₀ : ⊤ ≤ z₀ ⁻¹ᵁ W), IsUnit (ev z₀ W hz₀ (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N) g)) → ⊤ ≤ z₀ ⁻¹ᵁ U₀ TF.X Z) ∧ ∃ (z : Sp (Localization.Away g) ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z ∧ (∀ r, ev z W hz (((toBase TF Z).appLE U.1 W h.2.1).hom r) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.C r)) ∧ ∀ i, ev z W hz (cellCoord N i) = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away g) (MvPolynomial.X i) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section | exact GlobalTheory.LogPole.exists_cell_section | (intros; apply GlobalTheory.LogPole.exists_cell_section <;> assumption)
end

