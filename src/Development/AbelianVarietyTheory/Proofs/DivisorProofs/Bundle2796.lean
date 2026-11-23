module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGoodFormValuesMemScaledDualWeylLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleGoodFormValuesBoundedByClassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

open scoped Pointwise

namespace GlobalTheory.DefClassFin

def CCF : Prop :=
  ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, TC D σ β y (AfP p) z.1 → TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z, TC D σ β y (AfP p) z.1 →
        TC D σ β y ℚ_[p] z.2 →
        ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
          ∃ s ∈ S, ∃ u ∈ U, z = dg D p γ * s * u

theorem ccf_holds : CCF :=
  GlobalTheory.T.borel_finite_classNumber_centraliserTorus GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus GlobalTheory.classNumberFinite_holds

theorem finite_of_cover {H : Type} [Group H] (Γ K : Subgroup H) (S : Set H) (hS : S.Finite)
    (h : ∀ g : H, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, g = γ * s * k) :
    Finite (DoubleCoset.Quotient (Γ : Set H) (K : Set H)) := by
  haveI : Finite S := hS.to_subtype
  refine Finite.of_surjective (fun s : S => DoubleCoset.mk Γ K (s : H)) fun q => ?_
  obtain ⟨γ, hγ, s, hs, k, hk, e⟩ := h q.out
  refine ⟨⟨s, hs⟩, ?_⟩
  change DoubleCoset.mk Γ K s = q
  conv_rhs => rw [← DoubleCoset.out_eq' q]
  exact (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨γ, hγ, k, hk, e⟩

theorem cover_of_relIndex {A B : Type} [Group A] [Group B] (Γ : Subgroup (A × B)) (K₁ : Subgroup A)
    (K₂ K' : Subgroup B) (hK : K'.relIndex K₂ ≠ 0) (S : Set (A × B)) (hS : S.Finite)
    (h : ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K₁.prod K₂, g = γ * s * k) :
    ∃ S' : Set (A × B), S'.Finite ∧ ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S', ∃ k ∈ K₁.prod K', g = γ * s * k := by
  haveI : (K'.subgroupOf K₂).FiniteIndex := ⟨hK⟩
  let T : Set (A × B) := Set.range (fun c : K₂ ⧸ K'.subgroupOf K₂ => ((1 : A), ((c.out : K₂) : B)))
  have hT : T.Finite := Set.finite_range _
  refine ⟨S * T, hS.mul hT, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := h g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K₂) (⟨k.2, hk2⟩ : K₂)
  refine ⟨γ, hγ, s * (1, ((((⟨k.2, hk2⟩ : K₂) : K₂ ⧸ K'.subgroupOf K₂).out : K₂) : B)),
    Set.mul_mem_mul hs ⟨_, rfl⟩, (k.1, ((u : K₂) : B)⁻¹),
    Subgroup.mem_prod.2 ⟨hk1, K'.inv_mem (Subgroup.mem_subgroupOf.1 u.2)⟩, ?_⟩
  rw [hu]
  ext <;> simp [mul_assoc]

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

variable {p : ℕ} [Fact p.Prime]

theorem inT_of_TC (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : TC G.C G.star β 1 R z) : InT G R β 1 z :=
  ⟨h.1, by rw [map_one]; exact Commute.one_right _⟩

theorem TC_of_inT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : InT G R β 1 z) : TC G.C G.star β 1 R z :=
  ⟨h.1, by rw [← Algebra.TensorProduct.one_def]; exact Commute.one_right _⟩

theorem psiAway_psiAway_inv (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (w : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) : psiAway G x (psiAway G x⁻¹ w) = w := by
  simp only [psiAway_apply, inv_inv]
  exact Prod.ext (by group) rfl

theorem cover_KHT (P : CCF) (G : HTGroup p) (L : G.Level) (B : GlobalTheory.LKDef.DForm G) :
    ∃ S : Set (G.GAf × Gr G 1), S.Finite ∧ ∀ g : G.GAf × Gr G 1, ∃ γ ∈ B.emb.range, ∃ s ∈ S,
      ∃ k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw), g = γ * s * k := by
  set x := B.trivAf.choose with hxdef
  set t := B.trivAf.choose_spec.choose with htdef
  have hx : Triv G (AfP p) B.β x t := B.trivAf.choose_spec.choose_spec
  have hemb : ∀ y, B.emb y = (toAfF G B.β x t hx y, toP1 G B.β y) := fun y => rfl
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  let U : Subgroup (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (Subgroup.comap (psiAway G x) (L.K.toSubgroup.map (UPts G.star (AfP p)).subtype)).prod
      (Subgroup.comap (psiP G) (KHT p G.m G.n 1 G.Fw))
  obtain ⟨O₁, hO₁, h1O₁, hO₁U⟩ := exists_open_psiAway_mem_conj_level p G L B.β x t hx 1 1
  obtain ⟨O₂, hO₂, h1O₂, hO₂U⟩ := GlobalTheory.TorCls.OpenP.openp p G 1
  have hO : ∃ O : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
      ∀ z ∈ O, TC G.C G.star (B.β : G.C) 1 (AfP p) z.1 → TC G.C G.star (B.β : G.C) 1 ℚ_[p] z.2 → z ∈ U := by
    refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩, fun z hz h1 _ => Subgroup.mem_prod.2 ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk, e⟩ := hO₁U z.1 hz.1 (inT_of_TC G _ _ _ h1)
      exact ⟨k, hk, by simpa using e⟩
    · have := hO₂U z.2 hz.2
      simpa using this
  obtain ⟨S, hS⟩ := P G.C G.star (B.β : G.C) 1 p U hO

  let Neg : Prop := ∃ γ : G.Cˣ × ℚˣ, (γ.1 : G.C) * (B.β : G.C) * (G.star γ.1).unop =
    algebraMap ℚ G.C γ.2 * (B.β : G.C) ∧ (γ.2 : ℚ) < 0
  let gm : G.Cˣ × ℚˣ := if h : Neg then h.choose else 1
  let S₂ : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (S : Set _) ∪ (fun s => dg G.C p gm * s) '' (S : Set _)
  have hS₂ : S₂.Finite := S.finite_toSet.union (S.finite_toSet.image _)
  let Ψ : (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) →*
      ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 := (psiAway G x).prodMap (psiP G)
  let fH : G.GAf × Gr G 1 →* ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 :=
    (UPts G.star (AfP p)).subtype.prodMap (MonoidHom.id _)
  have hfH : Function.Injective fH := Prod.map_injective.2 ⟨Subtype.val_injective, Function.injective_id⟩
  refine ⟨fH ⁻¹' (Ψ '' S₂), (hS₂.image Ψ).preimage hfH.injOn, fun g => ?_⟩

  have hz₁ := inT_psiAway_inv_of_commute p G B.β x t hx 1 g.1 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₁
  obtain ⟨z₂, hz₂, hψ₂⟩ := _root_.GlobalTheory.TorCls.centraliser_at_p p G B.β B.sym 1 g.2 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₂
  set z₁ := psiAway G x⁻¹ (g.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) with hz₁def
  obtain ⟨γ, hγ, -, s, hs, u, hu, hz⟩ := hS (z₁, z₂) (TC_of_inT G _ _ _ hz₁) (TC_of_inT G _ _ _ hz₂)

  have key : ∃ δ : grp G B.β, ∃ s' ∈ S₂, (z₁, z₂) = dg G.C p (δ : G.Cˣ × ℚˣ) * s' * u := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hN : Neg := ⟨γ, hγ, hneg⟩
      have hgm : gm = hN.choose := dif_pos hN
      obtain ⟨hgmf, hgmn⟩ := hN.choose_spec
      rw [← hgm] at hgmf hgmn
      have hδ := form_mul_inv G.star (B.β : G.C) γ.1 gm.1 γ.2 gm.2 hγ hgmf
      have hδpos : (0 : ℚ) < ((γ.2 * gm.2⁻¹ : ℚˣ) : ℚ) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.2 hgmn)
      refine ⟨⟨γ * gm⁻¹, hδ, hδpos⟩, dg G.C p gm * s, Or.inr ⟨s, hs, rfl⟩, ?_⟩
      rw [hz]
      simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    · exact ⟨⟨γ, hγ, hpos⟩, s, Or.inl hs, hz⟩
  obtain ⟨δ, s', hs', hz'⟩ := key
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.1 hu
  obtain ⟨k₁, hk₁, ek₁⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hu1)
  have hk₂ : psiP G u.2 ∈ KHT p G.m G.n 1 G.Fw := Subgroup.mem_comap.1 hu2
  let k : G.GAf × Gr G 1 := (k₁, psiP G u.2)
  have hk : k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw) := Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩
  refine ⟨B.emb δ, ⟨δ, rfl⟩, (B.emb δ)⁻¹ * g * k⁻¹, ⟨s', hs', ?_⟩, k, hk, by group⟩
  have hΨz : Ψ (z₁, z₂) = fH g := by
    refine Prod.ext ?_ hψ₂
    exact psiAway_psiAway_inv G x _
  have hΨd : Ψ (dg G.C p (δ : G.Cˣ × ℚˣ)) = fH (B.emb δ) := by
    refine Prod.ext ?_ ?_
    · exact (toAfF_eq_psiAway G B.β x t hx δ).symm
    · exact (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G B.β δ).symm
  have hΨu : Ψ u = fH k := Prod.ext ek₁.symm rfl
  have e := congrArg Ψ hz'
  rw [map_mul, map_mul, hΨz, hΨd, hΨu] at e
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

theorem finite_doubleCoset : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level)
    (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  intro p _ G _ L K' hK B
  obtain ⟨S, hS, hcov⟩ := cover_KHT ccf_holds G L B
  obtain ⟨S', hS', hcov'⟩ := cover_of_relIndex B.emb.range L.K.toSubgroup _ K' hK.1.relIndex_ne_zero S hS hcov
  exact finite_of_cover _ _ S' hS' hcov'

end GlobalTheory.DefClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteFormBounds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormVal

theorem bigC_and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨A0, hA⟩ := h
  obtain ⟨B0, hB⟩ := h'
  refine ⟨max A0 B0, fun CF hCF => ?_⟩
  obtain ⟨C1, hC1⟩ := hA CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, hC2⟩ := hB CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, fun ε C hC => ?_⟩
  obtain ⟨x1, hx1⟩ := hC1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, hx2⟩ := hC2 ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x1 x2, ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hOK
  exact ⟨hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK,
    hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK⟩

theorem bigC_mono {Q Q' : ChQ} (h : BigC Q) (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (F : Face D A) (ch : Choice R) (C b : ℝ), Q F ch C b → Q' F ch C b) : BigC Q' := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun CF hCF => ?_⟩
  obtain ⟨c, h⟩ := h CF hCF
  refine ⟨c, fun ε C hC => ?_⟩
  obtain ⟨x, h⟩ := h ε C hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k => hQ F ch C large₂.sc.b (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j k)⟩

set_option maxHeartbeats 1600000 in
theorem form_fin_inf_of (h1 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))) (h2 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (σ : D.what₂.LL →+* ℂ) (x : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL),
  0 ≤ (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re ∧ ∀ y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    ((Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)) (h3 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)) : FinFormK ∧ InfFormK := by
  refine ⟨bigC_mono (bigC_and h1 h3) ?_, bigC_mono (bigC_and h2 h3) ?_⟩
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, hb, -⟩
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, by simp, fun s => by simpa using hb⟩, fun t w x hx y => ?_⟩
    exact hv t w x hx y
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, -, hK⟩ σ x y
    obtain ⟨hq, hy⟩ := hv σ x
    obtain ⟨u, e, hu⟩ := hy y
    exact ⟨u, e, hu.trans (mul_le_mul_of_nonneg_right hK hq)⟩

end GlobalTheory.FormVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClass
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem fibre_integral : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα
  have hol := _root_.GlobalTheory.ChernCalc.ptMap_isHolo F σ X Y f hf
  have hmet := _root_.GlobalTheory.ChernCalc.isMetricFr_pullGram F σ X Y ι m E E' φ f hf hR H hH
  have hgr := _root_.GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF F σ Y ι m E' _ hmet
  have hpb := (((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.2 _ _ (atlas Y σ) _ hol).2 1 α α).2.2.2 hα
  have hev := ((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.2.2.1 (Root m) (grF E' (pullGram E H φ f hf)) (fibrePoint m)
    fun x => (hgr x).1).1
  have hβ := (((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.1 1 _ _ hpb.1 hev)).2.1
  have key : ∀ s : ℤˣ, (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
      evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s Set.univ = (atlas X σ).part α s Set.univ := by
    intro s
    refine GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq _ _ (ptMap σ f hf) hol.1.measurable _ _ fun x => ?_
    have := X.smooth_str
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (σ := σ) x
    obtain ⟨A, hA⟩ := E.nonempty (under x)
    refine ⟨c.e.source ∩ interior {z | A ∈ E.S (under z)}, c.e.open_source.inter isOpen_interior,
      ⟨hc, mem_interior_iff_mem_nhds.2 (_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m 0 E x A hA)⟩, fun T hT hTU => ?_⟩
    exact GlobalTheory.FlagCell2.LocFib.part_preimage F σ X Y ι m E E' φ f hf hR H hH α hα hβ s c A _ (c.e.open_source.inter isOpen_interior)
      Set.inter_subset_left (fun z hz => (interior_subset (s := {z | A ∈ E.S (under z)}) hz.2 :)) T hT hTU
  rw [HolAtlas.integral, HolAtlas.integral, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key, key]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeries
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BaseCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem unitOff_inv_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v)⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨inv_ne_zero (mul_ne_zero hu0 hv0), n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹⁻¹ = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by
      rw [inv_inv, pow_add]; ring
    rw [e]; exact hn1.mul hm1

theorem exists_unif' (E : Type) [Field E] [NumberField E] (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (IsDedekindDomain.HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · have := PP.asIdeal.add_mem (hle h1) (hx1 PP)
      simpa using this
    · have := (PP.asIdeal ^ 2).sub_mem h h1
      simpa using this
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    refine ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · refine ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

theorem flatKer_holds : FlatKer := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV B hBg hB ξ ξR ω φ hK hQt N hN hNQ
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hflat⟩ := GlobalTheory.BaseCmp.flatTwoStep_holds D G Pl0 T0 A Ks R F hC i ξ B.de.chi ξR ω φ B hBg hB hK hK.chr
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif' D.host.E B.de.Q
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i B.de.Q eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := _root_.GlobalTheory.BaseCmp.dilKer_of_ne_zero D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hφ⟩ := _root_.GlobalTheory.BaseCmp.liftKer_of_ne D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hflat.1
  have hvT := hflat.2 Tm hTm
  have hφT := hφ Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    show Matrix.map (Matrix.map x fun w => incA D ((ϖ : D.host.E)⁻¹) * w) (fun w => incA D (ϖ : D.host.E) * w) = x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  have hvec : (princ B).vecBase = (κ * Gc)⁻¹ • ω (z, 1) φ := by
    rw [hφT, hact Tm hTm _ hSB]
    simp only [hcomp]
    have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i B.de.Q ξR eQ x) = Gc • flatDat R i B.de.Q ξR eQ := rfl
    rw [hsm, map_smul, ← hvT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]
  refine ⟨z, (κ * Gc)⁻¹, hz, unitOff_inv_mul' hκ hG, fun h P => ?_⟩
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  funext g
  rw [hvec, Pi.smul_apply, series_apply, series_apply, hB.fock_eq, hB.fock_eq, GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ z hz.2.1 1 (one_mem _) _ _ _ _ φ _ hth,
    map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem semiPosReg_of_eqOn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X}
    {φ ψ : Weight p σ B} {D : ℕ} (h : φ.SemiPosReg D)
    (e : ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y) : ψ.SemiPosReg D := by
  intro i c y hy ξ
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hm := ChartGlue.mem_over c.e hy.1 hy.2
  have ee : (fun v => (ψ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] (fun v => (φ.φ i (c.e.symm v) : ℂ)) :=
    Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv => by simp only [e i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr ee]
  exact h i c y hy ξ

theorem exists_addFn_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (M : MLine p σ) (D : ℕ) (hg : ∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    ∃ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (M.addFn u hu).φ.SemiPosReg D := by
  obtain ⟨ψ, hψ, hψp⟩ := _root_.GlobalTheory.weight_cInf_semiPos_of_generated k X p σ M.B M.φ.isLB hg
  obtain ⟨u, hu, he⟩ := _root_.GlobalTheory.Mix.weight_sub_cInf k X p σ M.B M.φ ψ M.cInf hψ
  exact ⟨u, hu, semiPosReg_of_eqOn (hψp D) fun i y hy => (he i y hy).symm⟩

end GlobalTheory.Mix

theorem GlobalTheory.Mix.side_eq_of_generated : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hz hL hgM hgN
  obtain ⟨u, hu, hMu⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg M (e + 1) hgM
  obtain ⟨v, hv, hNv⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg N (e + 1) hgN
  have hz' : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z h => (hz z h).symm
  have h1 := _root_.GlobalTheory.MetricIndep.side_sub_side_addFn hP F X p σ e hproj hdim L M N s hs t ht hz u hu
  have h2 := _root_.GlobalTheory.MetricIndep.side_sub_side_addFn hP F X p σ e hproj hdim L N (M.addFn u hu) t ht s hs hz' v hv
  have h3 := _root_.GlobalTheory.CycPair.side_le hP F X p σ e hproj hdim L (M.addFn u hu) (N.addFn v hv) s hs t ht hz hL hNv
  have h4 := _root_.GlobalTheory.CycPair.side_le hP F X p σ e hproj hdim L (N.addFn v hv) (M.addFn u hu) t ht s hs hz' hL hMu
  have d1 : divOfSec (M.addFn u hu).φ.isLB s hs = divOfSec M.φ.isLB s hs := rfl
  have d2 : divOfSec (N.addFn v hv).φ.isLB t ht = divOfSec N.φ.isLB t ht := rfl
  rw [d1, d2] at h3 h4
  rw [d1] at h2
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) → ¬ l ∣ deg h := by
  first | (exact @GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (exact GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (intros; apply GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel  <;> assumption)
end

