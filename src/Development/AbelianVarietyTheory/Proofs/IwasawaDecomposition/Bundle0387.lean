module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowMemDefiniteFamilyTypePart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.RowType

theorem row_mem_part : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (hL : Lam3 Z), (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ σ, uE (D.what₂.onb σ) ∈ R.EEp3 (Classical.choose hL (D.what₂.ft σ)) := by
  intro hPr D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hiso uE huE σ
  refine GlobalTheory.T.basis_row_rows_mem_eigensystem_type_part hPr D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hiso σ ?_
  have h := Y.tied.sharp.ft σ
  rw [Y.prtE] at h
  obtain ⟨z, hz, hz'⟩ := h
  have e : z = R.HE.e (uE (D.what₂.onb σ)) := by
    apply (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective
    exact hz'.trans (huE _)
  rw [Submodule.mem_comap, ← e]
  exact hz

theorem row_type : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ σ, ∃ p, uE (D.what₂.onb σ) ∈ R.EEp3 p ∧ ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p = ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) := by
  intro hPr D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hiso uE huE σ
  refine ⟨Classical.choose hL (D.what₂.ft σ), row_mem_part hPr D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hiso uE huE σ, ?_⟩
  have h2 := (Classical.choose_spec hL).2.1
  refine Finset.prod_congr rfl fun j hj => ?_
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hj' : j - 1 < D.R.m := by omega
  have e := h2 ⟨j - 1, hj'⟩ A3.A.μ0 (D.what₂.ft σ) (Or.inl Y.tup0) (hiso σ ⟨j - 1, hj'⟩)
  simp only [Fin.val_mk, Nat.sub_add_cancel hj1, Y.tup0] at e
  unfold RealDat3.lamN
  rw [dite_eq_left hj', e]
  rfl

end GlobalTheory.Mem.RowType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContainsRayFieldSub
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberRay

theorem containsRayField_sub (P : Pre) (δ : FieldDat P) (K : IntermediateField ℚ ℂ) [NumberField K]
    (hKE : K ≤ P.host.φ₀.toRatAlgHom.fieldRange) (hKR : K ≤ δ.ray) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hKR).toRingHom (modulus P) := by
  obtain ⟨hm, hNF, hray⟩ := δ.isRay
  letI := algOf P.host.φ₀ δ.ray hm
  obtain ⟨hab, hun, -, hart⟩ := hray
  haveI : IsGalois P.host.E δ.ray := hab.toIsGalois
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P) :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)
  let e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom
  let φKE : K →+* P.host.E :=
    ((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp
      (IntermediateField.inclusion hKE).toRingHom
  have hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom := by
    refine RingHom.ext fun x => Subtype.ext ?_
    have := congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))
    exact this
  rw [← hcomp]
  exact GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC

theorem weberSet_subset_ray : ∀ (P : Pre) (δ : FieldDat P) (L : PeriodPair), (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) → ∀ n : ℕ, Odd n → 3 ≤ n → n ∣ modulus P → weberSet L n ⊆ δ.ray := by
  intro P δ L hL n _ hn hdvd
  obtain ⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩ := GlobalTheory.FieldSize.exists_hostK P.R P.host
  have hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
  have hKR : K ≤ δ.ray := fun z hz => by
    obtain ⟨x, rfl⟩ := hKE hz
    exact δ.isRay.emb_mem x
  have hCK := containsRayField_sub P δ K hKE hKR
  obtain ⟨inst, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hP n hn
  haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)
  have hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0 := by
    exact_mod_cast modulus_ne_zero P
  haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _
  have hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_
    refine ((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hCK 𝔓 hc.1
    have h1' : (n : 𝓞 K) ∣ α - 1 := (Nat.cast_dvd_cast hdvd).trans h1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine _root_.GlobalTheory.SplitCompositum.ncard_eq_finrank_adjoin K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin δ.ray _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberRay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMulStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG (E := E) (ST := ST)), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  first | exact @GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | exact GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq | (intros; apply GlobalTheory.Mem.Col2.DiaPt.decoOf_dia_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ClsBij

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem ratAd_mem_ratPts (hc : CMData F E) (γ : UF E n) :
    ratAd F γ ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨ufGL E n γ, ?_, rfl⟩
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ

theorem exists_ratAd_eq (hc : CMData F E) {g : GL (Fin n) (AfE F E)}
    (hg : g ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ γ : UF E n, ratAd F γ = g := by
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨ratEquiv hc n ⟨r, hr⟩, ?_⟩
  show Formalism.UG.bc _ (ufGL E n _) = _
  rw [GlobalTheory.Mem.Col2.RatMove.ufGL_eq hc, MulEquiv.symm_apply_apply]

end SlopeTestRemainingChoices

theorem classes_bijective : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q C Λ Θ s U k' y hU hk' hlev hdense hpt hinj hsurj
  constructor
  · intro c c' hcc
    obtain ⟨γ, hγ, u, hu, he⟩ := (@DoubleCoset.eq _ _ _ _ (y c) (y c')).1 hcc
    have he' : (y c').1 = γ.1 * (y c).1 * u.1 := by rw [he]; rfl
    obtain ⟨δ, hδ⟩ := exists_ratAd_eq hc (Subgroup.mem_subgroupOf.1 hγ)
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q δ⁻¹ _ _ (hpt c')
    have e1 : ratAd F δ⁻¹ * ((y c').1 * k') = (y c).1 * u.1 * k' := by
      rw [he', ← hδ, ← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e1] at h1
    obtain ⟨h, θ, hhθ⟩ := (hlev (y c).1 u.1 (s c) _ (hpt c) h1).1 (Subgroup.mem_subgroupOf.1 hu)
    refine hinj c c' δ h θ ?_
    have e2 : ((δ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) =
        ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) := by
      simp
    rw [e2, mul_smul, hhθ, smul_smul]
    have e3 : ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((δ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = 1 := by
      simp
    rw [e3, one_smul]
  · intro q
    induction q using Quotient.inductionOn' with
    | h z =>
    obtain ⟨x, hx, p, hp⟩ := hdense z.1 z.2
    obtain ⟨c, γ, h, θ, hcp⟩ := hsurj p
    refine ⟨c, ?_⟩
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ⁻¹ _ _ hp
    have e1 : ((γ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p =
        ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c := by
      rw [← hcp, smul_smul]
      congr 1
      simp
    rw [e1] at h1
    have e2 : ratAd F γ⁻¹ * (z.1 * x * k') = (y c).1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x) * k' := by
      group
    rw [e2] at h1
    have hx' : (y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x ∈ U := (hlev (y c).1 _ (s c) _ (hpt c) h1).2 ⟨h, θ, rfl⟩
    let kk : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
      ⟨(y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹, hU (mul_mem hx' (inv_mem hx))⟩
    show DoubleCoset.mk _ _ (y c) = DoubleCoset.mk _ _ z
    refine (@DoubleCoset.eq _ _ _ _ (y c) z).2 ⟨z * kk⁻¹ * (y c)⁻¹, ?_, kk, Subgroup.mem_subgroupOf.2 (mul_mem hx' (inv_mem hx)), by group⟩
    rw [Subgroup.mem_subgroupOf]
    have e4 : ((z * kk⁻¹ * (y c)⁻¹ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (AfE F E))
        = ratAd F γ := by
      show z.1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹)⁻¹ * (y c).1⁻¹ = _
      rw [← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e4]
    exact ratAd_mem_ratPts hc γ

end GlobalTheory.Mem.Col2.ClsBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRowStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondElement_integral_support_lastRow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  first | exact @GlobalTheory.Mem.Dil.dia_data | exact GlobalTheory.Mem.Dil.dia_data | (intros; apply GlobalTheory.Mem.Dil.dia_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointFinitePartEqRealOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.FinPartLift

theorem exists_gfC_finHom_eq : ∀ {D : D7} (V : HSp D) (g : Bridge.Gf V), ∃ α ∈ GfC V, finHom V α = (g : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V g
  obtain ⟨β, hβ⟩ := g.2
  obtain ⟨α, hα, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V (Formalism.IndefR.Lev.finE V β) (GlobalTheory.LevSplit.finE_mem_UA V β)
  refine ⟨α, hα, ?_⟩
  rw [← hβ]
  apply Units.ext
  ext i j
  have h := congrArg (fun x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => x.val i j) e
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

end GlobalTheory.Mem.FinPartLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReductionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_couplingCoset_with_given_reduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)), ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  exact @GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd), ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  first | exact @GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | exact GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | (intros; apply GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ColAd

theorem exists_K1_isPtOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, p, by rwa [mul_inv_cancel_left]⟩
  have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
  rw [locM_mul, e]
  exact hp.fr P

end GlobalTheory.Mem.ColAd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem levFam_chr_exp : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  intro X n SG Λ
  have : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have : Finite ↥Λ.grp := inferInstance
  refine ⟨Nat.card ↥Λ.grp, Nat.card_pos, fun h => ?_⟩
  rw [← map_pow, pow_card_eq_one', map_one]

end GlobalTheory.Mem.Col2.TopCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_diagonal_basePoint_levelPrime : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  first | exact @GlobalTheory.Mem.Col2.BasePoint.exists_kStd | exact GlobalTheory.Mem.Col2.BasePoint.exists_kStd | (intros; apply GlobalTheory.Mem.Col2.BasePoint.exists_kStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaSupp

theorem castGL_bc_comm {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m k : ℕ} (h : m = k) (x : GL (Fin m) R) :
    castGL h (Formalism.UG.bc φ x) = Formalism.UG.bc φ (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

theorem finE_prV_eq_one {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V)
    (hα : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹)
    (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1 := by
  apply (castGL h.symm).injective
  rw [map_one, castGL_bc_comm]
  show Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α))) = 1
  rw [hα]
  have key : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (c x : G), f x = 1 → f (c * x * c⁻¹) = 1 := by
    intro G H _ _ f c x hx
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w)
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    Formalism.L2.Col.rll_put_ne n v w hw _
  exact key _ _ _ h1

end GlobalTheory.Mem.R3.LiftBrg.EtaSupp

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_suppAt : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  intro D V n _ h v Pb Ut d e C α hv he hα hη
  exact GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace V v Pb e hv he α hα fun w hw =>
    EtaSupp.finE_prV_eq_one V n h v Pb Ut d C α hη w hw

end GlobalTheory.Mem.R3.LiftBrg
end

