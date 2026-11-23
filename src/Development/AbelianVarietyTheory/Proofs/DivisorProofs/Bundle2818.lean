module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumMult

theorem gs_pow_mul_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (v u : Y ⟶ X) (N k : ℕ)
    (τ : LB.Sec (LB.LinComb L (K := Fin 2) ![v, u] ![(N : ℤ), -1])) (s : H0 L k) (i i' : Fin 1 → L.ι)
    (hle : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ LB.wchart L ![v, u] ![i' 0, i 0])
    (z : Y) (J' : (Y ⟶ X) → L.ι) (hz : z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i') (hJ : Good L z J')
    (hv : J' (𝟙 Y ≫ v) = i' 0) :
    gs (𝟙 Y) z (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
      ((Y.presheaf.map (homOfLE hle).op).hom (τ.f ![i' 0, i 0]) ^ k *
        (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i)).op).hom ((u.app (secChart L i)).hom (s.f i))) =
      sval τ (𝟙 Y) z J' ^ k * sval s (𝟙 Y ≫ u) z J' := by
  have hm : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L ![v, u] ![i' 0, i 0] := hle hz
  have hu : (𝟙 Y ≫ u) z ∈ secChart L i := hz.1
  have hv' : (𝟙 Y ≫ v) z ∈ L.U (i' 0) := Set.mem_iInter.1 hz.2 0
  have a0 : ∀ x y : Γ(Y, u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i'),
      gs (𝟙 Y) z _ (x ^ k * y) = gs (𝟙 Y) z _ x ^ k * gs (𝟙 Y) z _ y := fun x y => by
    rw [gs_eq _ _ _ hz, gs_eq _ _ _ hz, gs_eq _ _ _ hz, map_mul, map_mul, map_pow, map_pow]
  have a1 := gs_res (𝟙 Y) z hle hz (τ.f ![i' 0, i 0])
  have a2 := (gs_res (𝟙 Y) z (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤
          u ⁻¹ᵁ secChart L i) hz ((u.app (secChart L i)).hom (s.f i))).trans (gs_pull (𝟙 Y) u z _ hu (s.f i))
  rw [a0, a1, a2, sec_trans τ (𝟙 Y) z hm (hJ.mem _ (𝟙 Y)), sec_trans s (𝟙 Y ≫ u) z hu (hJ.mem _ _)]
  have e1 : trF (L := L) ![v, u] ![(N : ℤ), -1] (𝟙 Y) z ![i' 0, i 0] (fun k => J' (𝟙 Y ≫ (![v, u] : Fin 2 → _) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))))⁻¹ := by
    rw [trF, Fin.prod_univ_two]
    change gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U (J' (𝟙 Y ≫ v))) (L.g (i' 0) (J' (𝟙 Y ≫ v))) ^ (N : ℤ) *
      gm (𝟙 Y ≫ u) z (L.U (i 0) ⊓ L.U (J' (𝟙 Y ≫ u))) (L.g (i 0) (J' (𝟙 Y ≫ u))) ^ (-1 : ℤ) = _
    have gself : ∀ c : L.ι, c = i' 0 → gm (𝟙 Y ≫ v) z (L.U (i' 0) ⊓ L.U c) (L.g (i' 0) c) = 1 := by
      rintro c rfl; exact gm_self hL _ _ hv'
    rw [gself _ hv, one_zpow, _root_.one_mul, zpow_neg, zpow_one]
  have e2 : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (𝟙 Y ≫ u) z i
      (fun k => J' ((𝟙 Y ≫ u) ≫ (fun _ : Fin 1 => 𝟙 X) k)) =
      (gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u)))) ^ k := by
    simp only [trF, Fin.prod_univ_one]
    have gid : ∀ f : Y ⟶ X, f = 𝟙 Y ≫ u →
        gm f z (L.U (i 0) ⊓ L.U (J' f)) (L.g (i 0) (J' f)) = gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) := by
      rintro f rfl; rfl
    rw [gid _ (Category.comp_id _), zpow_natCast]
  rw [e1, e2]
  unfold sval
  generalize gm (𝟙 Y ≫ u) z _ (L.g (i 0) (J' (𝟙 Y ≫ u))) = A
  have hA : ((A⁻¹ : _ˣ) : Y.presheaf.stalk z) ^ k * ((A ^ k : _ˣ) : Y.presheaf.stalk z) = 1 := by
    rw [Units.val_pow_eq_pow_val, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  rw [mul_pow, _root_.mul_mul_mul_comm, hA, _root_.one_mul]

private theorem isUnit_gs_iff_mem {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine ((Y.mem_basicOpen ((r.app U).hom a) z h).symm).trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_mult_of_posN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) → GlobalTheory.MumMult.NonzeroAt D a N σ₀ x → ∃ m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i'), GlobalTheory.MumMult.MultAct U b N m ∧ GlobalTheory.MumMult.LeadPt U b m := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb N hN hP σ₀ x hx hnz
  obtain ⟨g, gsm, gtfe, gvan, g0⟩ := GlobalTheory.T.exists_mumford_formal_section_coefficient_family R hR.1 D a a' h h' hE N hN hP σ₀
  choose τ hτ using fun e => GlobalTheory.TwFamGlue.glue R hR.1 D a A G hG U e (b e) (hb.2.2.1 e) (N : ℤ) (-1) D.toPre.X id g gsm
  have hle : ∀ e (i i' : Fin 1 → U.LG.L.ι), multW U b e i i' ≤ LB.wchart U.LG.L
      ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![i' 0, i 0] := by
    intro e i i' y hy
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · simpa using Set.mem_iInter.1 hy.2 0
    · simpa using Set.mem_iInter.1 hy.1 0
  refine ⟨fun e i i' => ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hle e i i')).op).hom
    ((τ e).f ![i' 0, i 0]), ?_, ?_⟩
  · intro k hk f s hs
    obtain ⟨ρ, ρsm, ρtfe, hρ⟩ := GlobalTheory.T.exists_pullback_integralExpansion_formalEndomorphism R hR.1 D a a' h h' hE A G hG U b hb k s f hs
    obtain ⟨F, Fsm, Ftfe, hF⟩ := GlobalTheory.T.multiplier_power_mul_pullback_small_family R hR.1 D a a' h h' hE A G hG U b hb N k g ρ gsm ρsm gtfe ρtfe
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.TwBack.exists_intFam R hR.1 D a h h' (N * k) F Fsm Ftfe
    refine ⟨Φ, fun e i i' => ?_⟩
    obtain ⟨τ', hτ'1, hτ'2⟩ := hρ e
    obtain ⟨τ'', h1, h2⟩ := hF e (τ e) τ' (hτ e) hτ'2
    refine GlobalTheory.MumMult.chartExpOn_of_tExp R hR.1 D a A G hG U e (b e) (N * k) F Φ.f τ'' Fsm hΦ h2 i' _ _ ?_
    intro z J' hz hJ' hv
    rw [h1 _ _ z J' hJ', hτ'1 _ _ z J' hJ']
    exact gs_pow_mul_pull U.LG.isLB _ _ N k (τ e) s i i' (hle e i i') z J' hz hJ' hv
  · refine ⟨x, hx, fun y hy i i' hyW => ?_⟩
    choose J hJ using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (χ y)
    choose J' hJ' using fun χ : (thickObj R (maximalIdeal R) 0 G).left ⟶ G.left => exists_chart U.LG.isLB (χ y)
    have hx0 : IsUnit (sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J) := by
      have hm := Good.mem (L := D.toPre.P.L) hJ
        (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (𝟙 _ ≫ (U.gt 0).pG.left)
      have hyx : (𝟙 _ ≫ (U.gt 0).pG.left : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) y = x := hy
      refine (isUnit_gs_iff_mem _ y _ hm _).2 ?_
      rw [hyx] at hm ⊢
      exact hnz _ hm
    have hg0 : sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J = sval σ₀ (𝟙 _ ≫ (U.gt 0).pG.left) y J :=
      g0 _ (𝟙 _ ≫ (U.gt 0).q.left) y J hJ
    have hexp := hτ 0 {0} (fun β hβ => gvan β (by simpa using hβ)) _ (𝟙 _) y J J' hJ hJ'
    rw [Finset.sum_singleton] at hexp
    have hu : IsUnit (evalE U.toUnifPre (τ 0) (𝟙 _) y J J') := by
      rw [hexp]
      exact (hg0 ▸ hx0 : IsUnit (sval (g 0) (𝟙 _ ≫ (U.gt 0).pG.left) y J)).mul (Units.isUnit _)
    have hs : IsUnit (sval (τ 0) (𝟙 _) y J') := isUnit_of_mul_isUnit_right hu
    refine (isUnit_gs_iff_mem (𝟙 _) y _ hyW _).1 ?_
    have e := (gs_res (𝟙 _) y (hle 0 i i') hyW ((τ 0).f ![i' 0, i 0])).trans
      (sec_trans (τ 0) (𝟙 _) y (hle 0 i i' hyW) (Good.mem (L := U.LG.L) hJ' _ (𝟙 _)))
    exact e ▸ (Units.isUnit _).mul hs

end GlobalTheory.MumMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_nsmul_eq_of_tmap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B),
      tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  intro K _ l _ hl A B f φ hf
  refine exists_nsmul_eq_of_kills_torsion K A B f l hl fun x hx => ?_
  obtain ⟨t, ht⟩ := (tl_lev_surj_ker K l A 1).1 x (by rwa [pow_one])
  have h1 : (tmap l A B f t).lev 1 = x ≫ f.hom := by rw [lev_tmap, ht]
  rw [← h1, hf, LinearMap.smul_apply]
  exact ((tl_lev_surj_ker K l B 1).2 _).2 ⟨φ t, by rw [pow_one]⟩

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowClose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open Formalism.L2.Host (HChar)

namespace GlobalTheory.TopFlipNu

theorem exists_pow_close {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x c : w.adicCompletion E)
    (hx : Valued.v x = 1) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hK : IsCompact {y : w.adicCompletion E | Valued.v y ≤ 1} := by
    have := IsNonarchimedeanLocalField.isCompact_closedBall (w.adicCompletion E) 1
    convert this using 1
    ext y
    exact e.le_one_iff_le_one.symm
  have hv0 : Valued.v c ≠ 0 := by simpa using hc
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun y => {z | (z - y) * c⁻¹ ∈ w.adicCompletionIntegers E}) fun y _ =>
    ((Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).mul continuous_const)).mem_nhds
      (by simp)
  have h1 : ∀ n : ℕ, ∃ y : s, Valued.v (x ^ n - y) ≤ Valued.v c := fun n => by
    have : x ^ n ∈ {y : w.adicCompletion E | Valued.v y ≤ 1} := by simp [hx]
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hs this)
    refine ⟨⟨y, hy⟩, ?_⟩
    have h2 : Valued.v ((x ^ n - y) * c⁻¹) ≤ 1 := h
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hv0), one_mul] at h2
  choose f hf using h1
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := fun a b hab h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, by omega, ?_⟩
    have h3 := Valuation.map_sub_le _ (hf (a + k + 1)) (h ▸ hf a)
    have h4 : x ^ (a + k + 1) - f (a + k + 1) - (x ^ a - f (a + k + 1)) = x ^ a * (x ^ (k + 1) - 1) := by ring
    rwa [h4, map_mul, map_pow, hx, one_pow, one_mul] at h3
  obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' h, key b a h' h.symm]

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion E)ˣ) (hx : Valued.v (x : w.adicCompletion E) = 1) :
    ∃ k : ℕ, 0 < k ∧ χ.loc w x ^ k = 1 := by
  have hu := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hu
  obtain ⟨k, hk, h1⟩ := exists_pow_close w x
    (((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n) hx
    (pow_ne_zero _ (Units.ne_zero _))
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine h _ ?_ ?_
  · show Valued.v _ = 1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [map_pow, hu, ← WithZero.exp_nsmul] at h1
    rw [Units.val_pow_eq_pow_val]
    simpa using h1

theorem awayIm_unit {D : D7} {χ : HChar D.host.E} (hχ : LocIn D.what₂.embLL χ) {w : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion D.host.E)ˣ) (hx : Valued.v (x : w.adicCompletion D.host.E) = 1) (m : ℕ) :
    GlobalTheory.KappaArith.AwayIm D m (χ.loc w x : ℂ) := by
  obtain ⟨k, hk, h1⟩ := exists_pow_eq_one h x hx
  obtain ⟨ζ, hζ⟩ := hχ w x
  have h2 : ζ ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hk h2, hζ⟩

theorem chi_levelLe {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) : (G.ch.chiH i).LevelLe w 2 := by
  by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact fun x hx h3 => (G.ch.lev0 i h1 h2 w h).1 x hx (h3.trans (WithZero.exp_le_exp.2 (by omega)))
    · exact (G.ch.lev1 i h1 h2 w h).1
  · exact fun x hx _ => G.ch.unr i h1 h2 w h x hx

theorem nu_arith : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (x : ∀ w : Pl D.host.E, (Kw w)ˣ) (t : T),
      (∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1) →
      ∃ z : ℂ, GlobalTheory.KappaArith.AwayIm D (Qn G t) z ∧ ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
        z * ∏ w ∈ locPl G μ₀, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := by
  classical
  intro D T L sc G μ₀ hL hC i j x t hx
  have hQ : L.Q μ₀ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
    (hL.Q_ram μ₀ w).2 (Or.inl hw) (by rw [hL.xi_base]; intro x _; rfl)
  have h0 : locPl G μ₀ = G.pl.W0 := by rw [locPl, hQ]; simp
  have hsub : G.pl.W0 ⊆ locPl G t := fun w hw => by unfold locPl; simp [hw]
  have hf : ∀ w, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
      ((L.xiH t).loc w (x w) : ℂ) * (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w => by
    have loc_mul (a b : HChar D.host.E) : (a * b).loc w (x w) = a.loc w (x w) * b.loc w (x w) := rfl
    have loc_one : (1 : HChar D.host.E).loc w (x w) = 1 := rfl
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, loc_mul, hL.xi_base, loc_one,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
    ring
  have hb : ∀ w ∈ locPl G t, GlobalTheory.KappaArith.AwayIm D (Qn G t) (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w hw => by
    haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
    have hv : Valued.v (x w : Kw w) = 1 := e.eq_one_iff_eq_one.1 (hx w hw)
    have hv' : Valued.v (((x w)⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
    have a := awayIm_unit (hC.mu0 j) ((L.C.isMu0 j).tame w) (x w) hv (Qn G t)
    have b := awayIm_unit (hC.chi _ h1 h2) (chi_levelLe G h1 h2 w) (x w)⁻¹ hv' (Qn G t)
    have hm : muBase L (j + 1) = L.C.mu0 j := by rw [muBase, dite_eq_left j.2]
    convert a.mul b using 1
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, hL.xi_base, mul_one, hm, map_inv,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    exact div_eq_mul_inv _ _
  refine ⟨(∏ w ∈ locPl G t, ((L.xiH t).loc w (x w) : ℂ)) *
    ∏ w ∈ locPl G t \ G.pl.W0, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ), ?_, ?_⟩
  · exact (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w _ => GlobalTheory.KappaArith.awayIm_val hL (hC.xi t) _ w (x w)).mul
      (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w hw => hb w (Finset.mem_sdiff.1 hw).1)
  · rw [h0, mul_assoc, Finset.prod_sdiff hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hf w

end GlobalTheory.TopFlipNu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeParametersConstOneDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
noncomputable section
namespace GlobalTheory.BottomIPData

theorem isParamFun_one_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∃ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc _ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t
  exact ⟨_, GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar (GlobalTheory.Grid.neg A) X.rA.Λ _
    (GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1) (fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2)⟩

end GlobalTheory.BottomIPData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianModelProperOverThetaSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Poinc.exists_zhModel_proper_over_setup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X₁.M.pt ∧ (∀ z₁ : X₁.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z₁})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = c.y := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hti hproj
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hproj
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.T.finite_closure_theta_ratios_of_isCl' X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  have hpt : Y.pt ≫ q = X₁.M.pt :=
    hq.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  refine ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, ?_, ?_⟩
  · obtain ⟨U, hU, hiso⟩ := _root_.GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver X₁.o₁ X₁.Ω₁ Y X₁.M hO.proj q hq
    have : IsDedekindDomain X₁.o₁ := (inferInstance : ArithBase X₁.o₁ X₁.Ω₁).ded
    have := X₁.M.lft
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    exact GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z q (fun x => ⟨X₁.normal.isDomain_stalk x, X₁.normal.isIntegrallyClosed_stalk x⟩) U hU hiso
  · intro p _ z₁ c
    exact _root_.GlobalTheory.exists_lift_of_isProper_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M q hq hqp p c.y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HodgeDominates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_sec_detOm (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (hr : 1 ≤ Dw.p + Dw.q) (Y : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (w : Xo.XF c) {A : LB Y.X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow (FlagMod.detOm Y) m) A).Sec, Y.j w ∈ nonzeroLocus s := by
  obtain ⟨φs, hs, -⟩ := hS (max 1 (Module.finrank ℚ E * min Dw.p Dw.q)) (le_max_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y', BD, d, k, -, hk, hsm, -, hBD, -, hamp⟩ := hF E H Dw hr φ h₁ h₂ l Xo c
  have hY' := GlobalTheory.FanTheta.isLB_detOm_of_smooth Y' hr hsm
  obtain ⟨N, _, _, u, p, p', hu, hu', hp, hpt, e⟩ := exists_common_modification hE Y Y' hY hY'
  have e₁ : p (u w) = Y.j w := by rw [← hu]; rfl
  have e₂ : p' (u w) = Y'.j w := by rw [← hu']; rfl
  rw [← e₁]
  refine exists_sec_of_common p p' hp (u w) (fun W hW => ⟨Y'.j ''ᵁ (Y.j ⁻¹ᵁ W), ⟨w, (show Y.j w ∈ W from e₁ ▸ hW), e₂.symm⟩, ?_⟩) hY hY'
    (hamp hY') BD.isLB_lb e hk ?_ BD.canonical ?_ hA
  · rintro n ⟨w', hw', h⟩
    show p n ∈ W
    rw [hpt n w' h.symm]
    exact hw'
  · have h := cls_tens (isLB_lbPow hY' k) (isLB_dual BD.isLB_lb) (hamp hY').isLB
    rw [cls_lbPow hY', cls_dual BD.isLB_lb] at h
    exact (congrArg (· + _) h).trans (by abel)
  · rw [← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical, e₂]
    refine fun h => hBD _ h ?_
    have h' : Y'.jQ w ∈ pullback.fst Y'.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y'.t.G := by
      rw [Y'.ab_gen]; exact ⟨w, rfl⟩
    exact h'

theorem exists_lb_dominates (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (TF : TorFlag Xo c) :
    ∃ (ω : LB TF.Y.X) (hω : ω.IsLB), cls _ (TF.X.isLB_Llam (FlagMod.mu0 Dw)) = CechPic.pull TF.X.π (cls ω hω) ∧
      ∀ (w : Xo.XF c) (A : LB TF.Y.X), A.IsLB →
        ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, TF.Y.j w ∈ nonzeroLocus s := by
  have := TF.smooth
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hr
  · have hd : Dw.dim = 0 := by rw [Datum.dim, show Dw.q = 0 by omega, mul_zero]
    rw [hd] at this
    have : Etale TF.Y.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 this
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver TF.Y.proj
    have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified TF.Y.s
    have := IsFinite.of_isProper_of_locallyQuasiFinite TF.Y.s
    have : IsAffine TF.Y.X := isAffine_of_isAffineHom TF.Y.s
    refine ⟨_, LB.isLB_triv _, ?_, fun w A hA => ⟨1, one_pos, ?_⟩⟩
    · have he : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = 0 := by
        rw [FlagMod.unitaryWeightExponentVector_signatureWeightMuZero]
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · rfl
        · have := i.2
          have : Dw.mult σ = 0 := by unfold Datum.mult; split_ifs <;> omega
          omega
      refine Eq.trans (b := 0) ((cls_eq_zero_iff _).2 ⟨⟨fun _ => 1⟩, fun k k' => ?_⟩) (map_zero _).symm
      have hg : (TF.X.Llam (FlagMod.mu0 Dw)).g k k' = 1 :=
        Finset.prod_eq_one fun ix _ => by rw [he]; exact zpow_zero _
      rw [hg, map_one, map_one, mul_one]
    · obtain ⟨s, hs, -⟩ := exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_div (isLB_lbPow (LB.isLB_triv _) 1) hA)
        (Set.finite_singleton (TF.Y.j w)) (U := ⊤) (Set.subset_univ _)
      exact ⟨s, hs rfl⟩
  · have hY := GlobalTheory.FanTheta.isLB_detOm_of_smooth TF.Y hr
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) this)
    refine ⟨_, hY, ?_, fun w A hA => exists_sec_detOm hE hS hF hr TF.Y hY w hA⟩
    rw [← cls_pull hY _ (pull_isLB hY _), ← (cls_eq_iff TF.X.F.isLB_detOm _).2 (TF.X.F.detOm_iso_pull hY)]
    exact ((cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)).symm

end GlobalTheory.HodgeDominates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClassNumberCentraliserTorusSeparableStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classNumber_centraliserTorus_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → ∀ (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∀ r : G.GAf × Gr G 1, ∃ R : Finset (G.GAf × Gr G 1), ∀ c : G.GAf × Gr G 1, c * (toAfF G β x t hx y₀, toP1 G β y₀) = (toAfF G β x t hx y₀, toP1 G β y₀) * c → ∃ y : grp G β, y * y₀ = y₀ * y ∧ ∃ s ∈ R, ∃ k : G.GAf × Gr G 1, k.1 ∈ L.K.toSubgroup ∧ k.2 ∈ K' ∧ c * r = (toAfF G β x t hx y, toP1 G β y) * s * k := by
  first | (exact @GlobalTheory.CentCls.main) | (exact GlobalTheory.CentCls.main) | (intros; apply GlobalTheory.CentCls.main  <;> assumption)
end

