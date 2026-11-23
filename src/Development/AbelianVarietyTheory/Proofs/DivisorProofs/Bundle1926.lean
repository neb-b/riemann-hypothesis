module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_of_nadel_pairs : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.NadelApp.kawamataViehweg_complex | exact GlobalTheory.NadelApp.kawamataViehweg_complex | (intros; apply GlobalTheory.NadelApp.kawamataViehweg_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing : GlobalTheory.Published.AbelianDeRham → ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {g : ℕ}, Semi.IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  first | exact @GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | exact GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring | (intros; apply GlobalTheory.DeRham.ksRegular_of_isAbelianScheme_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSecOnto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem lbIso_sec_onto : ∀ (X : Scheme.{0}) (A B : LB X) (w : LB.Iso A B), A.IsLB → B.IsLB → w.IsGen →
    ∀ b : B.Sec, ∃ a : A.Sec, SecMaps w a b := by
  intro X A B w hA hB hw b
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB, fun p => ?_⟩
  obtain ⟨p, q⟩ := p
  have hV : B.U p ⊓ A.U q ≤ A.U q ⊓ B.U p := fun _ h => ⟨h.2, h.1⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec b hw hA hB q p)
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isoCand_rs] at e
  have hs : res (hV.trans (ReciprocityTheory.ChartRestriction.G.DVR.divLe (A := A) (B := B) q p)) (w.s (p, q)) = w.s (p, q) :=
    Units.ext (GlobalTheory.Cartier.resG_self _ _)
  rw [hs] at e
  have e2 : resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB).f q) =
      (((w.s (p, q))⁻¹ : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * resG X inf_le_left (b.f p) := by
    refine Eq.trans ?_ e
    exact (GlobalTheory.Cartier.resG_resG _ _ _).symm
  change resG X inf_le_left (b.f p) = ((@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * _
  simp only [id]
  rw [e2]
  exact (Units.mul_inv_cancel_left _ _).symm

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConst
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem cover_degree_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E), (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) (((δ k₂) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0 ∧ GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ (π k₂) (δ k₂)) → ∃ N : ℕ, 0 < N ∧ ∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  classical
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  letI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hC := GlobalTheory.T.complexFramedLifts_equiv_movedGroupCosets D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂ pr δ hπ
  have hK := GlobalTheory.T.card_framed_lifts_levelCover_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ₂
  have hfin : ∀ k (k₂ : {k₂ // pr k₂ = k}), Finite (↥((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ⧸ (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).subgroupOf ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) := by
    intro k k₂
    have h := (hπ k₂.1).2.2.2.1
    rw [k₂.2] at h
    exact Subgroup.index_ne_zero_iff_finite.1 h
  have hS : ∀ k (x' : ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).dom), (∑ᶠ k₂ : {k₂ // pr k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ) = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} ∧ Finite {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k x')} := by
    intro k x'
    obtain ⟨e⟩ := hC k x'
    haveI := hfin k
    refine ⟨?_, Finite.of_equiv _ e.symm⟩
    rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
    rfl
  have hne : ∀ y : FrPt Xo c (CAt σ₂), Nonempty {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} := by
    intro y
    obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hd
    obtain ⟨y₂, hy₂⟩ := hlift (CAt σ₂) (fun _ => rfl) y
    exact ⟨⟨y₂, hy₂⟩⟩
  by_cases hc : Nonempty (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp
  · obtain ⟨k₀⟩ := hc
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k₀)
    refine ⟨Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)}, ?_, fun k => ?_⟩
    · haveI := (hS k₀ ⟨x₀, hx₀⟩).2
      haveI := hne ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).un k₀ ⟨x₀, hx₀⟩)
      exact Nat.card_pos
    · obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k)
      rw [(hS k ⟨x, hx⟩).1]
      exact hK _ _
  · refine ⟨1, one_pos, fun k => (hc ⟨k⟩).elim⟩

end GlobalTheory.LevModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry


open GlobalTheory.LevelCarry in
theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVectorThreeStepDecomposition
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.LiftThreeStep

theorem omegaQ_union {D : D7} {a b : ℕ} {Sa St : Finset (Pl D.host.E)} (hd : Disjoint Sa St) (r : ℕ)
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ (Sa ∪ St) r ξ k y = omegaQ Sa r ξ k y * omegaQ St r ξ k y := by
  let g : Pl D.host.E → ℂ := fun PP =>
    if h : LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ k else 0
  have key : ∀ Q : Finset (Pl D.host.E), omegaQ Q r ξ k y = ∏ PP ∈ Q, g PP := by
    intro Q
    unfold omegaQ
    by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left h, ← Finset.prod_attach Q g]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [g]
      rw [dite_eq_left (h PP.1 PP.2)]
    · rw [dite_eq_right h]
      obtain ⟨PP, hPP⟩ := not_forall.1 h
      obtain ⟨hQ, hn⟩ := Classical.not_imp.1 hPP
      refine (Finset.prod_eq_zero hQ ?_).symm
      simp only [g]
      rw [dite_eq_right hn]
  rw [key, key, key, Finset.prod_union hd]

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem adjDat_union {Sa St : Finset (Pl D.host.E)} {ea et : AE D} (hg : IsIdemSum ea Sa) (hq : IsIdemSum et St)
    (hd : Disjoint Sa St) (he : IsIdemSum (ea + et) (Sa ∪ St)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    adjDat R i (Sa ∪ St) ξ (cA D (ea + et)) =
      GlobalTheory.TwoStepModel.tensorHalf (cA D et) (cA D ea) (adjDat R i Sa ξ (cA D ea)) (adjDat R i St ξ (cA D et)) := by
  have hA := GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have hB := GlobalTheory.TwoStepRed.redM_twoStep D _ _ (R.βV i) (R.βW i) Sa St ea et hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D ea) (cA D ea • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D et) (cA D et • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [GlobalTheory.TwoStepModel.tensorHalf_apply]
  unfold adjDat
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (ea + et)) x
  · have hx' : IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      rw [if_pos (And.intro hx hi), if_pos (And.intro (hcQ x) i2), if_pos (And.intro (hcg x) i1), omegaQ_union hd, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr St _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaQ_congr Sa _ ξ _ fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D ea) (cA D ea • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D ea • x))) :=
          fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D et) (cA D et • x) ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) (cA D et • x))) :=
          fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (ea + et)) x ∧ IsIntM (frMapAdj _ _ (R.βV i) (R.βW i) x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D et + cA D ea) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end

theorem thetaVector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i t _ Sa St hd hU eg ea et fg hg ha ht hfg
  obtain ⟨⟨hψ, -⟩, e, he, -⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨eQ, hq⟩ := (GlobalTheory.IdemFlip.idemSum_sub_and_flip D e _ (R.Q t) he Finset.subset_union_right).1
  have h2 : ThAt R i (cA D eQ) fg (adjDat R i (R.Q t) (R.xiR t) (cA D eQ)) (R.vP i t) :=
    GlobalTheory.ConjTwist.isThetaAt_vP_twoStep D G Pl0 T0 A Ks R F hC hG i t eg eQ fg hg hq hfg
  rw [← hU] at hq h2
  have hsum : eQ = ea + et := by
    rw [← GlobalTheory.ExportSeries.idem_eq hq, ← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq ht]
    exact Finset.sum_union hd
  subst hsum
  have hea := GlobalTheory.PlaceVec.idemSum_mul_self ha
  have het := GlobalTheory.PlaceVec.idemSum_mul_self ht
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hat : ea * et = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - hea - het
  have hca : cA D ea * cA D ea = cA D ea := by rw [← map_mul, hea]
  have hct : cA D et * cA D et = cA D et := by rw [← map_mul, het]
  have hta : cA D et * cA D ea = 0 := by rw [← map_mul, mul_comm, hat, map_zero]
  have hat' : cA D ea * cA D et = 0 := by rw [mul_comm, hta]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfa : infPart D (cA D ea) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha)
  have hinft : infPart D (cA D et) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ht)
  have hSB : ∀ (Q : Finset (Pl D.host.E)) (a : AE D), infPart D a = 0 →
      IsSBHalf a (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (adjDat R i Q (R.xiR t) a) :=
    fun Q a hinf => GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinf (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
      (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
      Q (fun y => omegaQ Q (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := h2
  have hc : cA D (ea + et) = cA D et + cA D ea := by rw [map_add (f := _), add_comm]
  have hc' : cA D (ea + et) = cA D ea + cA D et := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hct hca hta hΛ (hSB Sa _ hinfa) (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hca hct hat' hΛ (hc' ▸ hTe1)
  refine ⟨_, ⟨⟨_, hm2⟩, fun T' hT' => ?_⟩, ⟨_, hm1⟩, fun T' hT' => ?_⟩
  · exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hca hinfa hm2 hT' (hSB Sa _ hinfa)
  · rw [hTe2 Te hTe1, adjDat_union R i ha ht hd hq (R.xiR t)]
    exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hct hinft hm1 hT' (hSB St _ hinft)

end GlobalTheory.LiftThreeStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow

theorem hypS_of_isPolFibre : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  intro K K' _ _ f P P' ψ h hS
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ P.A P'.A (spMap f) ψ P.L P'.L P.isLB P'.isLB h.2.1 h.2.2.symm hS
end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.ValNe

theorem evalPt_eq_stalkClosedPointTo {Y : Scheme.{0}} {V : Type} [CommRing V] [IsLocalRing V] (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (GlobalTheory.Vanishing.ger _ hy g) = TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_ofSec_ne_zero_iff : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  intro K _ Y q L σ z i hi
  have hy : z (IsLocalRing.closedPoint K) ∈ L.U i := hi (Set.mem_univ _)
  have e : H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) = TangentOrigin.evalPt z _ hi (σ.f i) :=
    H0.val_ofSec z i le_top hi σ
  rw [e, ← evalPt_eq_stalkClosedPointTo z (L.U i) hi (σ.f i) hy, ← isUnit_iff_ne_zero,
    isUnit_map_iff, GlobalTheory.Vanishing.isUnit_ger_iff σ hy]

end GlobalTheory.ValNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalActionLinearInVectorStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_action_linear_in_vector : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  first | exact @GlobalTheory.LocOpLin.acts_lin | exact GlobalTheory.LocOpLin.acts_lin | (intros; apply GlobalTheory.LocOpLin.acts_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthOverDvrEqOverClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  first | exact @GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp | exact GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp | (intros; apply GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthStableUnderPrimePowPerturbationStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  first | exact @GlobalTheory.nuLocOf_pert | exact GlobalTheory.nuLocOf_pert | (intros; apply GlobalTheory.nuLocOf_pert <;> assumption)
end

