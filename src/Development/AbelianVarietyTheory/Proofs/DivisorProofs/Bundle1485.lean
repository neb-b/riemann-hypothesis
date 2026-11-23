module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowsSum3

theorem rowTypePart_map_finiteGroup_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (p : A3.fam3.base3.Ix) (g : G) :
    (R.EEp3 p).map (R.gE g) ≤ R.EEp3 p := by
  obtain ⟨hcore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hE
  simp only [RealDat3.EEp3, Submodule.map_iSup]
  refine iSup_le fun c => iSup_le fun hc => ?_
  refine le_trans ?_ (le_iSup₂_of_le c hc le_rfl)
  rw [hEE]
  exact GlobalTheory.RowPartStable.map_gE_le (s := 0) R.toRealDat F.lv2 hcore _ hSF c g

theorem iSup_EEp_inf_typeSp3 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (htop : (⨆ p, R.EEp3 p) = ⊤) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) :
    (⨆ p, (R.toCx3 F).EEp p ⊓ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
  have hsup : (⨆ p, (R.toCx3 F).EEp p) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x ∈ ⨆ p, R.EEp3 p := htop ▸ Submodule.mem_top
    exact Submodule.iSup_induction R.EEp3
      (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈ ⨆ p, (R.toCx3 F).EEp p) hx
      (fun p y hy => Submodule.mem_iSup_of_mem (p := (R.toCx3 F).EEp) p hy) (Submodule.zero_mem _)
      fun y z hy hz => Submodule.add_mem _ hy hz
  have hst : ∀ p g, ((R.toCx3 F).EEp p).map (R.gEx F g) ≤ (R.toCx3 F).EEp p := by
    rintro p g _ ⟨x, hx, rfl⟩
    exact rowTypePart_map_finiteGroup_le R F hC hE p g ⟨_, hx, rfl⟩
  have h := GlobalTheory.iSup_stable_inf_typeSpace (R.gEx F) P ((Units.map (A3.A.fam.v0.embedding : D.what₂.LL →+* ℂ).toMonoidHom).comp ψ)
    (R.toCx3 F).EEp (fun _ => True) hst
  simp only [iSup_pos, hsup, top_inf_eq] at h
  exact h.symm

theorem partsE : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ b, (R.toCx3 F).PartsE b := by
  intro hCR hHU D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hE hJ hOkH hPG hPos hkl hB b
  have hcar := _root_.GlobalTheory.Hk3.carries_of_rows_top hCR hHU R F hLI hOk hC hE hJ hPG hPos
  have htop := _root_.GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top R F hC hE (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R.toRealDat) hcar
  have hor := _root_.GlobalTheory.Div.inner_EEp3_eq_zero_of_ne R F hOk hC hOkH hkl hB
  refine ⟨fun p q hpq e he e' he' => ?_, ?_⟩
  · exact (congrArg (cj _) (hor p q hpq _ he.1 _ he'.1)).trans (map_zero _)
  · obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
    cases b
    · rw [h0]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _
    · rw [h1]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _

end GlobalTheory.RowsSum3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

theorem exists_ext (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    ∃ τ' : F →+* ℂ, ∀ c : 𝓞 F, τ' (c : F) = τ c := by
  have hinj : Function.Injective τ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker τ) hne (by simpa [RingHom.mem_ker] using hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, map_intCast] at hn
    simpa using hn
  refine ⟨IsFractionRing.lift hinj, fun c => ?_⟩
  exact IsFractionRing.lift_algebraMap hinj c

theorem root_cases {r z : ℂ} {tr nm : ℤ} (hd : tr ^ 2 - 4 * nm < 0) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (z ≠ r ↔ (starRingEnd ℂ) z = r) := by
  have hc : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hfac : ∀ x : ℂ, x ^ 2 - tr * x + nm = 0 → x = r ∨ x = tr - r := by
    intro x hx
    have : (x - r) * (x - (tr - r)) = 0 := by linear_combination hx - hr
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    have him : r.im = 0 := Complex.conj_eq_iff_im.1 h
    have hre := congrArg Complex.re hr
    have himr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [himr] at hre
    simp [sq] at hre
    have : ((2 * r.re - tr) ^ 2 : ℝ) = (tr : ℝ) ^ 2 - 4 * nm := by linear_combination 4 * hre
    have h2 : ((tr : ℝ) ^ 2 - 4 * nm) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * r.re - tr)]
  have hcr : (starRingEnd ℂ) r = tr - r := (hfac _ hc).resolve_left hne
  constructor
  · intro h
    have : z = tr - r := (hfac z hz).resolve_left h
    rw [this, ← hcr]; simp
  · intro h hzr
    rw [hzr] at h
    exact hne h

theorem lie_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  intro p _ D R _ b N σ ρ o h hL D' t Q e hU
  classical
  choose τ hτ using fun i => exists_ext D.F (σ.comp (b.t i))
  have hτ' : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c => hτ i c
  obtain ⟨hrank, hcov⟩ := _root_.GlobalTheory.UPel.HT.LieType.lieEigen_rank_cover p D R b N σ ρ o h hL D' t Q e hU τ hτ'
  have hsum := GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul p D D' ρ Q hU.2.1
  set r := σ b.ρ with hrdef
  have hr : r ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hω : (D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hτω : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have := congrArg (fun x : 𝓞 D.F => τ' (x : D.F)) hω
    simpa using this
  have key : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ≠ r ↔ ((starRingEnd ℂ).comp τ') (D.ω : D.F) = r :=
    fun τ' => root_cases D.disc_neg hr (hτω τ')

  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := hτ' i x
      have h2 := hτ' j x
      rw [hij] at h1
      simp [RingHom.mem_ker, ← h1, ← h2]
    rw [b.comax i j hne] at hle
    have : (1 : R) ∈ RingHom.ker σ := hle Submodule.mem_top
    simp [RingHom.mem_ker] at this
  have hτA : ∀ i, τ i (D.ω : D.F) = r := fun i => by rw [hτ', b.t_ω]
  set d : (D.F →+* ℂ) → ℕ := fun τ' => Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ') with hd

  have hzero : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = r → τ' ∉ Finset.univ.image τ → d τ' = 0 := by
    intro τ' h1 h2
    have hbot : eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = r • u := by
        have := hu D.ω
        rw [h1] at this
        exact this
      have hmem := hcov u hu'
      have hle : (⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) ≤ ⨆ τ'' ∈ Finset.univ.image τ, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'' := by
        refine iSup_le fun i => ?_
        exact le_biSup (fun τ'' => eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'') (Finset.mem_image_of_mem τ (Finset.mem_univ i))
      have := (_root_.GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) _ τ' h2).le_bot ⟨hu, hle hmem⟩
      simpa using this
    simp [hd, hbot]
  have hA : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ i, (D.m : ℂ) * σ (b.t i c) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hA' : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) =
      ∑ i, (D.m : ℂ) * (starRingEnd ℂ) (σ (b.t i c)) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hconj : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) := by
    intro c
    refine Finset.sum_nbij' (fun τ' => (starRingEnd ℂ).comp τ') (fun τ' => (starRingEnd ℂ).comp τ') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have := (key x).1 (by simpa using hx)
      simpa using this
    · intro x hx
      have hx' : x (D.ω : D.F) = r := by simpa using hx
      have : ¬ ((starRingEnd ℂ).comp x) (D.ω : D.F) = r := by
        exact fun h => (key x).2 h hx'
      simpa using this
    · intro x _; ext; simp
    · intro x _; ext; simp
    · intro x _; simp
  intro c
  have htr : (ρ (algebraMap (𝓞 D.F) D.O c)).trace = ∑ τ' : D.F →+* ℂ, (d τ' : ℂ) * τ' (c : D.F) := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) c
  rw [htr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r)]
  have hB : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), ((D.m : ℂ) * D.n * τ' (c : D.F) -
        (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F)) := by
    refine Finset.sum_congr rfl fun τ' _ => ?_
    have := hsum τ'
    have h' : (d τ' : ℂ) + d ((starRingEnd ℂ).comp τ') = D.m * D.n := by exact_mod_cast this
    linear_combination τ' (c : D.F) * h'
  rw [hB, Finset.sum_sub_distrib, hconj c, hA c, hA' c]
  have e1 : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.m : ℂ) * D.n * τ' (c : D.F) =
      D.m * ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.n : ℂ) * τ' (c : D.F) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  simp only [← Finset.mul_sum]
  ring

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormConjVacuumEqRankProductMul
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ConjVacuumPower

theorem even_rank (R : Ranks) (l : ℕ) : Even (R.N l) := by
  unfold Ranks.N
  exact R.k_even.add ((R.t_odd.add_one).mul_left l)

theorem logThAt_eq_mul : ∀ (D : D7) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] (σ₀ : K →+* ℂ) (R : Ranks) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D D.host.ccK → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK dl → TaylorLogMetric.IsChi D χ → B.VecP χ → ThetaFieldData B cD σ₀ R M → ∀ ρ : M →ₐ[ℚ] ℂ, ∃ lt : ℝ, ∀ i < R.m, logThAt B M ρ (R.N i) (R.N (i + 1)) = (R.N i : ℝ) * (R.N (i + 1) : ℝ) * lt := by
  intro D dl B χ cD K _ σ₀ R M _ hadm hpsi hcur hdel hχ hV hH ρ
  have hc : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨hcur, hdel⟩
  have hY := GlobalTheory.ExponentsFinite.yFinite D B.γ₀ B.kc
  have hT := _root_.GlobalTheory.FamilyTieProof.familyTie D _ dl B χ hadm hpsi hcur hdel hχ hY
  have hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK dl) M := hH.2.1
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ dl hc).2 M ρ hD.2.1 hD.2.2
  refine ⟨(TaylorLogMetric.fF D : ℝ) * Real.log (StandardLatticesGL3.nrm1Sq (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl))
    (GL3Theta.th0 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl)) t')), fun i hi => ?_⟩
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.NatAtStd.eNat_std D _ dl B χ hχ hV _ _ (even_rank R i) (even_rank R (i + 1))
  have hE := hT _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE
  have hs : ∀ n, StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := fun n => by
    letI := D.host.cmStar
    exact GlobalTheory.NatAtStd.isSD_pi _ n
  have h := (GlobalTheory.ConjNorm.useNorm_all D _ dl hc _ B.t0 _ _ _ _ (hs _) (hs _) ((even_rank R i).mul_right _) _ hE M ρ hD
    (hH.2.2.2 i hi) t' ht').1
  unfold logThAt
  erw [h]
  rw [Real.log_pow]
  push_cast
  ring

end GlobalTheory.ConjVacuumPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_descent_unramified_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K'), IsUnit g.det → (∀ σ ∈ D, ∃ h : Matrix (Fin n) (Fin n) W, g.map σ = h.map (algebraMap W K') * g) → ∃ (h : Matrix (Fin n) (Fin n) W) (k : Matrix (Fin n) (Fin n) K), IsUnit h.det ∧ k.map (algebraMap K K') = h.map (algebraMap W K') * g := by
  first | exact @GlobalTheory.matrix_descent_unramified | exact GlobalTheory.matrix_descent_unramified | (intros; apply GlobalTheory.matrix_descent_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactBlockLeviSecond
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

namespace GlobalTheory.CuspSmooth

theorem conj_list_prod {G : Type} [Group G] (g : G) (l : List G) :
    g⁻¹ * l.prod * g = (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.prod_cons, List.map_cons]; rw [← ih]; group

theorem mem_Sm_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        (fun x => ψ (ι x * g₀)) ∈ GlobalTheory.CuspRep.Sm E d := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW K hK S l d h ι hι hd _ _ _ ψ hψ g₀ _ g
  classical
  refine _root_.GlobalTheory.SecondKind.contDiffOn_of_prodExp E d _ {X | ∃ v, ∀ i j, ∀ u, u ≠ v → X i j u = 0} ?_ ?_
  · rw [eq_top_iff]
    intro X _
    have e : X = ∑ v : InfinitePlace E, (Matrix.of fun i j => Pi.single v (X i j v)) := by
      ext i j u
      rw [Matrix.sum_apply, Finset.sum_apply]
      simp [Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.subset_span ⟨v, fun i j u hu => by simp [Pi.single_apply, hu]⟩
  · intro k X hX y hy
    choose v hv using hX
    have hγ : ∀ i, IsRealLine σ J (fun t : ℝ => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X i))) * g₀) :=
      fun i => GlobalTheory.EisCont.CentreFinite.isRealLine_conj hcm
        (_root_.GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp F E σ hcm n J hJ r Xf Yf hW l d h ι hι (v i) (X i) (hv i)) g₀
    have hs := hψ.1.smooth k _ hγ (ι (g * GlobalTheory.CuspRep.infGL E d hy.unit) * g₀)
    convert hs using 2 with t
    set P : GL (Fin d) (GlobalTheory.CuspRep.Cinf E) := (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).prod
    have hP : (P : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) =
        (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod := by
      simp only [P]
      rw [← Units.coeHom_apply, map_list_prod, List.map_ofFn]
      rfl
    have hU : GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) =
        GlobalTheory.CuspRep.toL (hy.unit * P).val := by
      rw [Units.val_mul, hP]
      congr 2
    rw [hU, GlobalTheory.CuspRep.chart_val]
    have e3 : (List.ofFn fun i => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t i • X i))) * g₀) =
        ((List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).map (ι.comp (GlobalTheory.CuspRep.infGL E d))).map
          (fun a => g₀⁻¹ * a * g₀) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [e3, ← conj_list_prod, ← map_list_prod]
    simp only [P, map_mul, MonoidHom.comp_apply, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionComp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on appLE_resG appLE_appLE appLE_of_eq)

theorem lin_f {R : Type} [CommRing R] {m N : ℕ} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (j : Fin (m + 1))
    (i : Fin (N + 1)) :
    (lin a j).f i = ∑ n, GlobalTheory.AbLaw.cst (PSpace.str R N) (chart R N i) (a j n) * GlobalTheory.ProjSpace.ratio R N i n := by
  refine (GlobalTheory.LinChange.sum_f (H := O1 R N) _ i).trans (Finset.sum_congr rfl fun n _ => ?_)
  refine (GlobalTheory.LB.smul_f (L := O1 R N) _ _ i).trans ?_
  rw [GlobalTheory.LinChange.resG_cst]
  exact congrArg (_ * ·) (coord_f R N n i)

end GlobalTheory.SpanVA

theorem GlobalTheory.SpanVA.toProj_eq_liftDom_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  intro R _ X f H m N s t a _ hs ht hst h
  have hg : GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N = f := by
    rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N)
    (GlobalTheory.SpanVA.iSup_nonzeroLocus_secPull_lin a) (GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h)
    (t := s) hs ?_
  · rw [hg] at e
    exact e
  intro z
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i :=
    inf_le_left.trans (GlobalTheory.ProjSpace.toProj_preimage_chart f t ht i).ge
  have hk : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ⁻¹ᵁ
      ((GlobalTheory.ProjSpace.O1 R N).pull (GlobalTheory.SpanVA.dom a).ι).U (fun _ => i) := by
    refine hW.trans (le_of_eq ?_)
    erw [GlobalTheory.Cartier.pull_U]
    rw [← Scheme.Hom.comp_preimage, GlobalTheory.SpanVA.liftDom_fac]
    rfl
  refine ⟨nonzeroLocus (t i) ⊓ H.U l, ⟨hi, hl⟩, fun _ => i, hk, l, inf_le_right, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X inf_le_right ((t i).f l),
    fun j => ?_⟩
  have key : ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a j) (GlobalTheory.SpanVA.dom a).ι).f (fun _ => i)) =
      ((GlobalTheory.ProjSpace.toProj f t ht).appLE (GlobalTheory.ProjSpace.chart R N i) _ hW).hom ((GlobalTheory.SpanVA.lin a j).f i) := by
    show ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG _ _ (((GlobalTheory.SpanVA.dom a).ι.app _).hom ((GlobalTheory.SpanVA.lin a j).f i))) = _
    rw [GlobalTheory.ProjSpace.appLE_resG, Scheme.Hom.app_eq_appLE, GlobalTheory.ProjSpace.appLE_appLE]
    exact congrArg (fun ψ => ψ.hom ((GlobalTheory.SpanVA.lin a j).f i))
      (GlobalTheory.ProjSpace.appLE_of_eq (GlobalTheory.SpanVA.liftDom_fac a _ h) (GlobalTheory.ProjSpace.chart R N i) _ _ hW)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, GlobalTheory.SpanVA.lin_f, map_sum, hst j, GlobalTheory.LinChange.sum_f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst]
  erw [GlobalTheory.LinChange.appLE_cst (PSpace.str R N) (GlobalTheory.ProjSpace.toProj f t ht) hW (a j n)]
  rw [GlobalTheory.ProjSpace.toProj_str]
  change _ = _ * (_ * GlobalTheory.ProjSpace.pullRatio (GlobalTheory.ProjSpace.toProj f t ht) _ i hW n)
  rw [GlobalTheory.ProjSpace.pullRatio_toProj_on, GlobalTheory.ProjSpace.secRatio_on (t i) (t n) l inf_le_left inf_le_right]
  ring
end

