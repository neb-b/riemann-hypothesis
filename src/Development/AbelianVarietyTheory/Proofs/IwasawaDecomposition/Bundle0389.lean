module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => _root_.GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel g L t ht hζ htL d V _ hd ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine _root_.GlobalTheory.SerCmp.hasLabelO_of_hasLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) (_root_.GlobalTheory.SerCmp.canonList_of_cuspidal_list g) r τ f hτ
      · exact _root_.GlobalTheory.GLq.isCuspOf_label_unique_allPrimes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact _root_.GlobalTheory.SerCmp.hasLabel_of_hasLabelO g L O hcusp (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [_root_.GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianChart_complex_rational_integral_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → ValuationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY (fun _ => True) chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  first | exact @GlobalTheory.Mem.Col2.TC.val_tied | exact GlobalTheory.Mem.Col2.TC.val_tied | (intros; apply GlobalTheory.Mem.Col2.TC.val_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.InertiaTwoPlaces

open Polynomial

theorem fix_of_fix_integral {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (h : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs1, e⟩ := ReciprocityTheory.Gal.exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have h2 : σ s * σ x = σ t := by rw [← map_mul, e]
  rw [h s hs, h t ht, ← e] at h2
  exact mul_left_cancel₀ hs0 h2

theorem eq_of_mem_Ine_of_mem_Ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A,
    σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  intro E Ω _ _ _ _ _ A A' P hA hA' σ hσ hσ' hne
  by_contra hAA
  apply hne
  apply fix_of_fix_integral
  intro b hb
  by_contra hD
  have hD0 : σ b - b ≠ 0 := sub_ne_zero.mpr hD
  set f0 := minpoly ℤ b with hf0
  have hf0m : f0.Monic := minpoly.monic hb
  have hf0b : Polynomial.aeval b f0 = 0 := minpoly.aeval ℤ b
  set d := f0.natDegree with hd
  have hnat : ∀ n : ℕ, A'.valuation (n : Ω) ≤ 1 := fun n => ReciprocityTheory.Gal.valuation_natCast_le_one A' n
  obtain ⟨m, hdm, hmu⟩ : ∃ m : ℕ, d ≤ m ∧ A'.valuation (m : Ω) = 1 := by
    by_cases h1 : A'.valuation (d : Ω) = 1
    · exact ⟨d, le_rfl, h1⟩
    refine ⟨d + 1, Nat.le_succ d, ?_⟩
    by_contra h2
    have l1 : A'.valuation (d : Ω) < 1 := lt_of_le_of_ne (hnat d) h1
    have l2 : A'.valuation ((d + 1 : ℕ) : Ω) < 1 := lt_of_le_of_ne (hnat _) h2
    have : A'.valuation (((d + 1 : ℕ) : Ω) - (d : Ω)) < 1 := by
      rw [sub_eq_add_neg]
      exact Valuation.map_add_lt _ l2 (by rw [Valuation.map_neg]; exact l1)
    push_cast at this
    simp at this
  set f1 : Polynomial ℤ := Polynomial.X ^ (m - d) * f0 with hf1
  have hf1m : f1.Monic := (Polynomial.monic_X_pow _).mul hf0m
  have hf1d : f1.natDegree = m := by
    rw [hf1, (Polynomial.monic_X_pow _).natDegree_mul hf0m, Polynomial.natDegree_X_pow, ← hd]
    omega
  have hf1b : Polynomial.aeval b f1 = 0 := by simp [hf1, hf0b]
  have hσA : σ ∈ Dec (F := E) A := Ine_le_Dec A hσ
  have hbD : IsIntegral ℤ (σ b - b) :=
    (hb.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)).sub hb
  have hc : IsIntegral ℤ ((σ b - b) ^ m) := hbD.pow m
  have hc0 : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ hD0
  obtain ⟨e0, he0i, he0A, he0A'⟩ := GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other E Ω A A' P hA hA' (Ne.symm hAA) _ hc hc0
  obtain ⟨e, hei, hef, heA, heA'⟩ := GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element E Ω A A' σ hσ' e0 _ he0i he0A he0A'
  obtain ⟨ys, hcard, hys, hprod⟩ := GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial E Ω A' σ hσ' b e m f1 hei hef heA' hmu hf1m hf1d hf1b
  have hbm : A.valuation (b ^ m - 1) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
  have h1 : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    rw [Valuation.map_mul, ← Valuation.map_pow]
    calc A.valuation e * A.valuation (b ^ m - 1) ≤ A.valuation e * 1 := mul_le_mul_of_nonneg_left hbm zero_le'
      _ = A.valuation e := mul_one _
      _ < _ := heA
  have h2 : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hcard]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyf := (hys y hy).2
    have e1 : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hyf]; ring
    rw [e1, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg, GlobalTheory.T.iwasawaDecomposition_fact E Ω A σ hσA, max_self]
  rw [← hprod] at h2
  exact absurd h2 (not_le.mpr h1)

end GlobalTheory.InertiaTwoPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem decoRaw_mul_levelIwahori_reduction {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {n : ℕ} [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

theorem isPtOf_mul_J0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g z p p' h
  refine ⟨fun hp hp' => ⟨?_, fun he => ?_⟩, fun hQ hp hz hr => ?_, fun hQ hg => ?_⟩
  · rintro ⟨hz, hr⟩
    apply Subtype.ext
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco] at h1
    exact h1
  · have hx : decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 h := by
      rw [(near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco, he]
      rfl
    obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hp'.uni hp.uni h hx
    have e : (g * z)⁻¹ * g = z⁻¹ := by group
    have hz : z ∈ J0 hc n ST := by
      have h1 := inv_mem hJ
      rwa [e, inv_inv] at h1
    refine ⟨hz, ?_⟩
    have e' : (⟨(g * z)⁻¹ * g, hJ⟩ : J0 hc n ST) = (⟨z, hz⟩ : J0 hc n ST)⁻¹ := Subtype.ext e
    rw [e', map_inv] at hr
    rw [← hr, inv_inv]
  · refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q (g * z) _ hQ).2
      ⟨mul_mem hp.uni (congruence_le_adelic_unitary hc n ST hz), ?_⟩
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco] at h1
    exact h1.symm
  · obtain ⟨q, hq⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
    exact ⟨q, (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q g q hQ).2 ⟨hg, hq.deco.symm⟩⟩

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.OkVals

theorem isConjAt_embLL (B : Base) : Formalism.DivisionValues.IsConjAt (InfinitePlace.mk B.embLL) := fun a => by
  rcases InfinitePlace.embedding_mk_eq B.embLL with e | e
  · rw [e]
    exact B.starLL_cx a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, B.starLL_cx a]

theorem ev_of_forall {p : Top.Ctx → Prop} (h : ∀ K, p K) : Top.Ev p :=
  ⟨1 / 100, by norm_num, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem large_coefficientField_contains_twist_values : Top.EvLg fun _ B f T => ∀ (px : PreX B.toPre) (I : Col2.ColIn B px) (hX : B.fields.Ok), I.Ok → I.C = f →
    Set.range I.xi = T.set f → ValsIn I ∧ ∀ U Xg tr, (∀ χ ∈ Xg, IsAbsIrrChar χ) → (famC I hX U Xg tr).fam3.Ok3 1 := by
  obtain ⟨Sv, hSv, hV⟩ := _root_.GlobalTheory.Mem.Col2.exists_roots_valsIn
  obtain ⟨So, hSo, hF⟩ := _root_.GlobalTheory.Mem.HFld.heckeFields
  unfold Top.EvLg
  refine ev_of_forall fun _ => ?_
  unfold Top.large₂
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f F F₀ Ξ => Sv P Ξ ∪ So P f F F₀ Ξ, fun _ _ _ z hz => absurd hz (Finset.notMem_empty z), ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact hSv P Ξ z h
    · exact hSo P f F F₀ Ξ z h
  intro B f T _ hH _ _ px I hX hOk hC hR
  have hL : ∀ z ∈ Sv B.toPre (Set.range I.xi) ∪ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC := by
    rw [hR, hC]
    exact hH.2
  refine ⟨hV B px I hOk fun z hz => hL z (Finset.mem_union_left _ hz), fun U Xg tr hirr => ?_⟩
  have hFI := hF B px I hX hOk fun z hz => hL z (Finset.mem_union_right _ hz)
  have hC2 := _root_.GlobalTheory.Mem.R3.Comm.rows_lifts_comm B px I hX hOk
  have key : ∀ τ : TupU I U, ∃ a : I.ι, I.tup a = τ.1 := fun τ => ⟨_, tup_ixOf I τ⟩

  have hH3 : ColHyp3 B.wts I.Ch I.sel (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ := by
    refine ⟨⟨isConjAt_embLL B, hirr, fun τ => Formalism.L2.Col.heckeComm_of_paths _ _ Formalism.L2.Col.pathCount_symmetric_holds, fun τ => ?_,
      fun j τ => Formalism.L2.Col.heckeComm_of_paths _ _ Formalism.L2.Col.pathCount_symmetric_holds, fun j τ => ?_⟩, fun τ => ?_, fun τ => ?_, fun j τ => ?_, fun j τ => ?_⟩
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).1
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inr i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).2 j
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inr i)
  have h := colFam3_ok B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr hH3
  exact h

end GlobalTheory.Mem.R3.OkVals

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.Mem.Col2

theorem stpTop_groupClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  have hne : B.R.m + 1 ≠ B.R.m := by omega
  have hY : ∀ p : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.2 = ∅ := by
    intro p
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hne] at h
    exact h
  have hpt : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.1 = q.1.1 → p = q := by
    intro p q h
    exact Subtype.ext (Prod.ext h ((hY p).trans (hY q).symm))
  have hcos : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn p = cosetIn q := by
    intro p q
    funext P
    ext z
    simp [cosetIn, hY p, hY q]
  set S := I.stp u a B.R.m with hS
  have key : ∀ (T : GStep B.fields.E B.fields.K (B.R.N B.R.m)) (b : T.β) (x y : T.D b) (g : T.G b), g • x = y →
      (Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) x) = Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) y :=
    fun T b x y g h => Quotient.sound ⟨g⁻¹, by rw [← h]; exact inv_smul_smul g x⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_ | al, hb⟩, q⟩
    · refine ⟨Equiv.refl _, fun κ => ⟨rfl, rfl, rfl, rfl, hcos _ _, fun h => hpt _ _ h⟩⟩
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · rintro ⟨⟨_ | al, hb⟩, q⟩ ⟨⟨_ | al', hb'⟩, q'⟩ γ h θ hγ
    · have e1 : S.act ⟨none, hb⟩ (γ, h, θ) (S.rep ⟨⟨none, hb⟩, q⟩) = S.rep ⟨⟨none, hb'⟩, q'⟩ := hpt _ _ hγ
      have hq : q = q' := by
        have h1 := S.rp_spec ⟨none, hb⟩ q
        have h2 := S.rp_spec ⟨none, hb'⟩ q'
        rw [← h1, ← h2]
        exact key S _ _ _ _ e1
      subst hq
      rfl
    · exact absurd (hb'.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · intro p
    obtain ⟨pt, hpt'⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m) p
    let b : S.β := Idx.top I.sel (I.tup a) (I.idx a) le_rfl
    obtain ⟨g, hg⟩ := S.exists_mv b pt
    refine ⟨S.cl b pt, g.1, g.2.1, g.2.2, ?_⟩
    exact (congrArg (fun x : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m => x.1.1) hg).trans hpt'
  · haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
    obtain ⟨pt, -⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m)
      (DecoF.base _ _ _ _ _)
    exact ⟨S.cl (Idx.top I.sel (I.tup a) (I.idx a) le_rfl) pt⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruence
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

open GlobalTheory.TopStep
open GlobalTheory.Mem.Col2.PtExist (mat)

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_dep_eq_exp (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : ∃ N : ℕ, dep P c = WithZero.exp (-(N : ℤ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, dep P c = WithZero.exp m := ⟨_, (WithZero.exp_log (dep_ne_zero c)).symm⟩
  have h1 : m ≤ 0 := by
    have := dep_le_one (P := P) c
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  refine ⟨(-m).toNat, ?_⟩
  rw [hm, Int.toNat_of_nonneg (by omega), neg_neg]

variable [StarRing E]

theorem sm_of_lqPrinc {P : HeightOneSpectrum (𝓞 E)} {N c : ℕ} (hd : dep P c = WithZero.exp (-(N : ℤ))) {g : Sp E n ≃ₗ[E] Sp E n}
    (h : lqPrinc P N g) : Sm Valued.v (dep P c) (ratM P g - 1) := by
  intro i j
  have e : (ratM P g - 1) i j = algebraMap E (P.adicCompletion E) ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) := by
    have e1 : mat g i j = LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) i j := by
      rw [LinearMap.toMatrix'_apply]
      rfl
    simp only [Matrix.sub_apply, map_sub, ratM, Matrix.map_apply, e1, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, valued_algebraMap, hd]
  exact h i j

end Loc

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TC

theorem levQ_top_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  intro B X I a
  choose N hN using fun P : I.Q a => exists_dep_eq_exp P.1 (topDep B.R (I.cst a).M + 1)
  refine ⟨N, fun P => (hN P).le, fun P g hg => ?_⟩
  have hk : g ∈ GlobalTheory.TopStep.prinCong (B.R.N B.R.m) P.1 (topDep B.R (I.cst a).M + 1) := mem_prinCong_of_sm g (sm_of_lqPrinc (hN P) hg)
  have e : (I.Tp a).levQ B.R.m = levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) := topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  rw [e]
  exact ⟨prinCong_le_levCong _ _ _ hk, levCong_lam_prinCong _ _ _ hk⟩

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem rhoT_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (t x : GL (Fin n) (AfE F E)) (hx : rhoP F P x = 1) : rhoT F P t x = 1 := by
  show rhoP F P (MulAut.conj t⁻¹ x) = 1
  rw [MulAut.conj_apply, map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem topChi_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  intro F E K _ _ _ _ _ _ _ n Q σ U t Θ d hd N hdN hΘ
  letI : IsOneApply (topU U t Θ d →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (topU U t Θ d →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  constructor
  · intro h
    choose m hm0 hm using h
    refine ⟨∏ P : Q, m P, Finset.prod_pos fun P _ => hm0 P, fun x => ?_⟩
    unfold topChi
    rw [MonoidHom.inv_apply, inv_pow, prod_apply, ← Finset.prod_pow, Finset.prod_eq_one, inv_one]
    intro P _
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ P)
    rw [hc, pow_mul, MonoidHom.comp_apply, ← map_pow, MonoidHom.comp_apply]
    have e : locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x) ^ m P = 1 :=
      hm P _
    rw [e, map_one, one_pow]
  · intro x hx
    unfold topChi
    rw [MonoidHom.inv_apply, prod_apply, Finset.prod_eq_one, inv_one]
    intro P _
    have e : ((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x = 1 :=
      Subtype.ext (rhoT_eq_one P.1 t x.1 (hx P))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_one, map_one]

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionOntoFiniteGroupSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U), Function.Surjective (LiftBrg.ActQ.redQ X I U L eG i t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.redQ_surjective <;> assumption)
end

