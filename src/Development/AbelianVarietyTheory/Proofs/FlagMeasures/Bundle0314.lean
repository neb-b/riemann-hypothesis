module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteClassesLatticesFixedFramePartBoundedScale
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatClassFin

theorem fg_of_le_fg {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    {N L : Submodule (𝓞 K) V} (hL : L.FG) (h : N ≤ L) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_of_le_right h]
  rw [← e]; exact h1.map _

theorem frame_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast i =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem classes_fin : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D T T' F F' hpos A N d c hN hd hc
  classical
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hcompl : IsCompl U W := GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos
  let hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E := (VS D).hT.domRestrict₁₂ W W
  have hWs : hW.IsSymm := (VS D).herm.domRestrict W
  have hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x) := fun x hx =>
    hpos x.1 x.2 (fun h => hx (Subtype.ext h))
  obtain ⟨s, hslat, hs⟩ := GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc
  let ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V := W.subtype.restrictScalars (𝓞 D.host.E)
  let Mof : Submodule (𝓞 D.host.E) ↥W → LV D := fun L => A ⊔ L.map ι
  let Sset : Set (LV D) :=
    ⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}
  have hfin : Sset.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun L _ => ?_
    by_cases hA : A.FG
    · by_cases hL : L.FG
      · refine (_root_.GlobalTheory.finite_lattices_between_of_smul_le (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_
        rintro Λ' ⟨-, -, h1, h2⟩
        exact ⟨h1, h2⟩
      · exact Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)
    · exact Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)
  refine ⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩
  set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'
  have hL'lat : Submodule.IsLattice D.host.E L' := GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W
  have hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
    fun x hx y hy => hdΛ x.1 hx y.1 hy
  have hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) →
      (c : D.host.E) • y ∈ L' := by
    intro y hy
    show (c : D.host.E) • (y : (VS D).V) ∈ Λ
    exact hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)
  obtain ⟨M₀, hM₀s, g, hg, hgM⟩ := hs L' hL'lat hsc hdu
  have hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V) :=
    fun x y => hg x y
  obtain ⟨γ, hγi, hγU, hγW⟩ := _root_.GlobalTheory.OrthExt.extend_isom (VS D) U hcompl g hgiso
  have hγH : γ ∈ H0 F F' :=
    ⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)),
      fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩
  have hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ := fun x => by
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; rfl
  have hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U := fun a ha => by
    rw [← hAΛ] at ha; exact ⟨ha.1, ha.2⟩
  refine ⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩
  rw [Set.Finite.mem_toFinset]
  have hAfg : A.FG := by
    rw [← hAΛ]; exact fg_of_le_fg hΛ.fg inf_le_left
  have hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι := by
    intro w hw hwΛ
    have h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by rw [hgM]; exact hwΛ
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearEquiv.eq_symm_apply]
    show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w
    rw [hγW, LinearEquiv.apply_symm_apply]
  refine Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩
  · refine sup_le (fun a ha => ?_) ?_
    · rw [hmem, hγU a (hAsub a ha).2]; exact (hAsub a ha).1
    · rintro _ ⟨m, hm, rfl⟩
      rw [hmem]
      show γ ((m : ↥W) : (VS D).V) ∈ Λ
      rw [hγW]
      have h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by
        rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]; exact hm
      rw [hgM] at h1
      exact h1
  · intro x hx
    rw [hmem] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (hNΛ _ hx)
    have hx' : (N : D.host.E) • x = γ.symm u + γ.symm w := by
      rw [← map_add (f := _), huw, map_smul, LinearEquiv.symm_apply_apply]
    have hu' : γ.symm u = u := by
      rw [LinearEquiv.symm_apply_eq]; exact (hγU u hu.2).symm
    rw [hx', hu']
    refine Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)
    rw [← hAΛ]; exact hu

end GlobalTheory.LatClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GlobProj

theorem weak_integral_prod {X Y H : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (R : X × Y → (H →L[ℂ] H)) (A : X → (H →L[ℂ] H)) (B : Y → (H →L[ℂ] H))
    (hR : ∀ g k, R (g, k) = A g * B k) (hn : ∀ z v, ‖R z v‖ = ‖v‖)
    (a : X → ℂ) (e : Y → ℂ) (ha : Integrable a μ) (he : Integrable e ν) (P E : H →L[ℂ] H)
    (hP : ∀ x y : H, ⟪x, P y⟫_ℂ = ∫ g, a g * ⟪x, A g y⟫_ℂ ∂μ)
    (hE : ∀ x y : H, ⟪x, E y⟫_ℂ = ∫ k, e k * ⟪x, B k y⟫_ℂ ∂ν) (x y : H)
    (hm : AEStronglyMeasurable (fun z => ⟪x, R z y⟫_ℂ) (μ.prod ν)) :
    ⟪x, (P.comp E) y⟫_ℂ = ∫ z, (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ ∂(μ.prod ν) := by
  have hbd : ∀ z, ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun z => by
    calc ‖⟪x, R z y⟫_ℂ‖ ≤ ‖x‖ * ‖R z y‖ := norm_inner_le_norm x _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hae : Integrable (fun z : X × Y => a z.1 * e z.2) (μ.prod ν) := ha.mul_prod he
  have hint : Integrable (fun z : X × Y => (a z.1 * e z.2) * ⟪x, R z y⟫_ℂ) (μ.prod ν) := by
    refine Integrable.mono' (hae.norm.mul_const (‖x‖ * ‖y‖)) (hae.aestronglyMeasurable.mul hm) ?_
    refine ae_of_all _ fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd z) (norm_nonneg _)
  rw [integral_prod _ hint, ContinuousLinearMap.comp_apply, hP]
  congr 1
  funext g
  dsimp only
  have h1 : ⟪x, A g (E y)⟫_ℂ = ∫ k, e k * ⟪x, R (g, k) y⟫_ℂ ∂ν := by
    rw [← ContinuousLinearMap.adjoint_inner_left (A g) (E y) x, hE]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, hR, ContinuousLinearMap.mul_apply]
  rw [h1, ← integral_const_mul]
  congr 1
  funext k
  ring

theorem conv_prod (B : RowsAut) (a : B.I.Ginf → ℂ) (P : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (ha : Integrable a (muInf B.I)) (hP : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) a P) :
    B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) (P.comp B.Re) ∧
      ∀ T, B.I.IsRConv B.μf B.fund B.R (fun x => a x.1 * B.e x.2) T → T = P.comp B.Re := by
  obtain ⟨-, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : SFinite (muInf B.I) := by unfold muInf; infer_instance
  have hE := B.Re_spec
  have key : ∀ x y : B.I.L2 B.μf B.fund, ⟪x, (P.comp B.Re) y⟫_ℂ =
      ∫ g, (fun z : B.I.GA => a z.1 * B.e z.2) g * ⟪x, B.R g y⟫_ℂ ∂(B.I.muA B.μf) := by
    intro x y
    have hm : AEStronglyMeasurable (fun z => ⟪x, B.R z y⟫_ℂ) ((muInf B.I).prod B.μf) :=
      (continuous_const.inner (hcont y)).aestronglyMeasurable
    exact weak_integral_prod (muInf B.I) B.μf B.R (fun g => B.R (g, 1)) (fun k => B.R (1, k))
      (fun g k => by rw [← hmul, Prod.mk_mul_mk, mul_one, one_mul]) (fun z v => hnorm z v)
      a B.e ha hE.1 P B.Re hP.2 hE.2 x y hm
  have hint : Integrable (fun z : B.I.GA => a z.1 * B.e z.2) (B.I.muA B.μf) := ha.mul_prod hE.1
  refine ⟨⟨hint, key⟩, fun T hT => ?_⟩
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [hT.2, key]

theorem comm_of_isOpOf {G L : Type} [MeasurableSpace G] [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    {μ : Measure G} {π : G → (L →L[ℂ] L)} {φ : G → ℂ} {P E : L →L[ℂ] L} (hP : IsOpOf μ π φ P)
    (hE : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ) (hc : ∀ g, E.comp (π g) = (π g).comp E) (y : L) :
    P (E y) = E (P y) := by
  refine ext_inner_left ℂ fun x => ?_
  rw [hP.2 x (E y), ← hE x (P y), hP.2 (E x) y]
  congr 1
  funext g
  congr 1
  have h := congrArg (fun T : L →L[ℂ] L => T y) (hc g)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h, hE]

theorem abstract_count {G H L : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (σ : G → (H →L[ℂ] H)) (π : G → (L →L[ℂ] L)) (w : H)
    (hw : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H))
    (P E : L →L[ℂ] L) (hPP : ∀ y, P (P y) = P y) (hPs : ∀ x y : L, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ)
    (hEE : ∀ y, E (E y) = E y) (hEs : ∀ x y : L, ⟪E x, y⟫_ℂ = ⟪x, E y⟫_ℂ)
    (hPE : ∀ y, P (E y) = E (P y)) (hc : ∀ g, E.comp (π g) = (π g).comp E)
    (hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : H →L[ℂ] L, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w)
    (S : Submodule ℂ (H →L[ℂ] L))
    (hS : ∀ A, A ∈ S ↔ ∃ A₀ : H →L[ℂ] L, (∀ g : G, A₀ ∘L σ g = π g ∘L A₀) ∧ E ∘L A₀ = A) :
    IsOrthProjOnto (P.comp E) (LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) ∧
      (∀ A ∈ S, (P.comp E) (A w) = A w) ∧
      (∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y) ∧
      Nonempty (S ≃ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L)) := by
  have hQQ : ∀ y, P (E (P (E y))) = P (E y) := fun y => by rw [← hPE, hPP, hEE]
  have hSi : ∀ A ∈ S, ∀ g, A ∘L σ g = π g ∘L A := by
    intro A hA g
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    rw [ContinuousLinearMap.comp_assoc, hA₀ g, ← ContinuousLinearMap.comp_assoc, hc g,
      ContinuousLinearMap.comp_assoc]
  have huniq : ∀ A ∈ S, ∀ A' ∈ S, A w = A' w → A = A' := by
    intro A hA A' hA' h
    refine ContinuousLinearMap.ext_on hw ?_
    rintro _ ⟨g, rfl⟩
    have e1 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A hA g)
    have e2 := congrArg (fun T : H →L[ℂ] L => T w) (hSi A' hA' g)
    simp only [ContinuousLinearMap.comp_apply] at e1 e2
    show A (σ g w) = A' (σ g w)
    rw [e1, e2, h]
  have hfix : ∀ A ∈ S, (P.comp E) (A w) = A w := by
    intro A hA
    obtain ⟨A₀, hA₀, rfl⟩ := (hS A).1 hA
    obtain ⟨y, hy⟩ := (hr (A₀ w)).2 ⟨A₀, hA₀, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [hEE, hPE, ← hy, hPP]
  have hex : ∀ y, (P.comp E) y = y → ∃! A, A ∈ S ∧ A w = y := by
    intro y hy
    simp only [ContinuousLinearMap.comp_apply] at hy
    obtain ⟨io, hio, hyw⟩ := (hr y).1 ⟨E y, hy⟩
    have hEy : E y = y := by rw [← hy, ← hPE, hEE]
    have hmem : E ∘L io ∈ S := (hS _).2 ⟨io, hio, rfl⟩
    have hval : (E ∘L io) w = y := by rw [ContinuousLinearMap.comp_apply, ← hyw, hEy]
    refine ⟨E ∘L io, ⟨hmem, hval⟩, ?_⟩
    rintro A ⟨hA, hAw⟩
    exact huniq A hA _ hmem (by rw [hAw, hval])
  refine ⟨⟨?_, ?_, rfl⟩, hfix, hex, ?_⟩
  · ext y
    simp only [ContinuousLinearMap.comp_apply]
    exact hQQ y
  · intro x y
    simp only [ContinuousLinearMap.comp_apply]
    rw [hPs, hEs, ← hPE]
  · let f : S →ₗ[ℂ] LinearMap.range ((P.comp E : L →L[ℂ] L) : L →ₗ[ℂ] L) :=
      { toFun := fun A => ⟨(A : H →L[ℂ] L) w, LinearMap.mem_range.2 ⟨(A : H →L[ℂ] L) w, hfix A A.2⟩⟩
        map_add' := fun A B => Subtype.ext rfl
        map_smul' := fun c A => Subtype.ext rfl }
    have hinj : Function.Injective f := fun A A' h =>
      Subtype.ext (huniq _ A.2 _ A'.2 (congrArg Subtype.val h))
    have hsurj : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ (by
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
        exact hQQ z)
      exact ⟨⟨A, hA⟩, Subtype.ext hAw⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem globalProj_holds : GlobalProj := by
  intro B d hd hint
  obtain ⟨hReP, hReC, -⟩ := GlobalTheory.IdemProj.re_orth_proj B
  obtain ⟨hU, -, hF, hnw, hph⟩ := _root_.GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨h1, hmul, hnorm, hcont, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : (muInf B.I).IsHaarMeasure := by unfold muInf; infer_instance
  haveI : ∀ v, (muG (B.I.ε v)).IsMulRightInvariant := fun v =>
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ (B.I.ε v) g⟩
  haveI : (muInf B.I).IsMulRightInvariant := by unfold muInf; infer_instance
  let σh : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := hU.1, map_mul' := hU.2.1 }
  let πh : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) :=
    { toFun := fun g => B.R (g, 1), map_one' := h1
      map_mul' := fun a b => by rw [← hmul, Prod.mk_mul_mk, mul_one] }
  have hDne : ((∏ v, d v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
  have hsq : ∀ x y : B.Hs, Integrable (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) (muInf B.I) ∧
      ∫ g, ‖⟪y, σh g x⟫_ℂ‖ ^ 2 ∂(muInf B.I) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / (∏ v, d v) := by
    intro x y
    obtain ⟨hi, he⟩ := hF.2 x y x y
    have hre : ∀ g, RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) = ‖⟪y, σh g x⟫_ℂ‖ ^ 2 := by
      intro g
      rw [RCLike.star_def, RCLike.mul_conj]
      norm_cast
    have hfun : (fun g => ‖⟪y, σh g x⟫_ℂ‖ ^ 2) =
        fun g => RCLike.re (⟪y, B.σs g x⟫_ℂ * star ⟪y, B.σs g x⟫_ℂ) := funext fun g => (hre g).symm
    rw [hfun]
    refine ⟨hi.re, ?_⟩
    rw [integral_re hi, he, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have hc : ((‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v : ℝ) : ℂ) = (‖x‖ : ℂ) ^ 2 * (‖y‖ : ℂ) ^ 2 / ((∏ v, d v : ℝ) : ℂ) := by
      push_cast; ring
    rw [← RCLike.ofReal_re (K := ℂ) (‖x‖ ^ 2 * ‖y‖ ^ 2 / ∏ v, d v)]
    congr 1
    exact hc.symm
  have hintw : Integrable (fun g => ⟪B.tens B.w, σh g (B.tens B.w)⟫_ℂ) (muInf B.I) := by
    refine Integrable.mono' (hint.norm.const_mul (∏ v, d v)⁻¹)
      (continuous_const.inner (hU.2.2.2 (B.tens B.w))).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    show ‖⟪B.tens B.w, B.σs g (B.tens B.w)⟫_ℂ‖ ≤ (∏ v, d v)⁻¹ * ‖ph B d g‖
    rw [hph g, norm_mul, norm_star, Complex.norm_of_nonneg hF.1.le, ← mul_assoc,
      inv_mul_cancel₀ hF.1.ne', one_mul]
  obtain ⟨-, -, hPA⟩ := projAbs_holds B.I.Ginf (muInf B.I) B.Hs σh (fun g x => hU.2.2.1 g x) hU.2.2.2
    (∏ v, d v) hF.1 hsq (B.tens B.w) hnw hintw
  obtain ⟨⟨P, hP⟩, hPall⟩ := hPA (B.I.L2 B.μf B.fund) πh (fun g x => hnorm _ x)
    (fun x => (hcont x).comp (continuous_id.prodMk continuous_const))
  obtain ⟨hSP, -, -, hrange⟩ := hPall P hP
  have hphG : phG (∏ v, d v) σh (B.tens B.w) = ph B d := funext fun g => (hph g).symm
  have hPop : IsOpOf (muInf B.I) (fun g => B.R (g, 1)) (ph B d) P := by
    refine ⟨by rw [← hphG]; exact hP.1, fun x y => ?_⟩
    rw [hP.2 x y, hphG]
    rfl
  have hPP : ∀ y, P (P y) = P y := fun y => by
    have h := congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hSP.isIdempotentElem.eq
    simpa using h
  have hPs : ∀ x y : B.I.L2 B.μf B.fund, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_left P y x, hSP.isSelfAdjoint.adjoint_eq]
  have hr : ∀ v, (∃ y, P y = v) ↔ ∃ io : B.Hs →L[ℂ] B.I.L2 B.μf B.fund,
      (∀ g : B.I.Ginf, io ∘L B.σs g = B.R (g, 1) ∘L io) ∧ v = io (B.tens B.w) := fun v => by
    have h := Set.ext_iff.1 hrange v
    simp only [SetLike.mem_coe, LinearMap.mem_range, ContinuousLinearMap.coe_coe, Set.mem_setOf_eq] at h
    exact h
  have hS : ∀ A, A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re ↔
      ∃ A₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund, (∀ g : B.I.Ginf, A₀ ∘L B.σs g = B.R (g, 1) ∘L A₀) ∧
        B.Re ∘L A₀ = A := by
    intro A
    simp only [AutInst.eHom, Submodule.mem_map]
    constructor
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
    · rintro ⟨A₀, hA₀, rfl⟩
      exact ⟨A₀, hA₀, rfl⟩
  have hPE : ∀ y, P (B.Re y) = B.Re (P y) := comm_of_isOpOf hPop hReP.2.1 hReC
  have hEE : ∀ y, B.Re (B.Re y) = B.Re y := fun y =>
    congrArg (fun T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => T y) hReP.1
  have hwd := hF.dense_span_orbit (B.tens B.w) (norm_ne_zero_iff.1 (by rw [hnw]; exact one_ne_zero))
  have hAC := abstract_count B.σs (fun g => B.R (g, 1)) (B.tens B.w) hwd P B.Re hPP hPs hEE hReP.2.1
    hPE hReC hr _ hS
  have hconv := conv_prod B (ph B d) P hint hPop
  refine ⟨hReP, hReC, ⟨P.comp B.Re, hconv.1⟩, fun T hT => ?_⟩
  obtain rfl := hconv.2 T hT
  obtain ⟨h1', h2', h3', ⟨eq⟩⟩ := hAC
  refine ⟨h1', h2', h3', fun hfd => ?_, (LinearEquiv.finrank_eq eq).symm⟩
  haveI := hfd
  exact LinearEquiv.finiteDimensional eq

end GlobalTheory.GlobProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TauNorm

theorem exists_bound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, ‖L B‖ ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c, hc0, fun B => ?_⟩
  have hB : L B = ∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, ← map_smul, Matrix.smul_single]
  have hle : ∀ i j, ‖L (Matrix.single i j (1 : ℂ))‖ ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖L (Matrix.single i j (1 : ℂ))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hB]
  calc ‖∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ))‖
      ≤ ∑ i, ∑ j, ‖B i j‖ * ‖L (Matrix.single i j (1 : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul _ _).le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
    _ = c * ∑ i, ∑ j, ‖B i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exp_dOp_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, P * B * Q ≠ 0 → Real.exp (GlobalTheory.Count.dOp (P * B * Q)) ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun B => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))
      map_add' := fun B B' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a B => by simp }
  obtain ⟨c, hc, h⟩ := exists_bound L
  refine ⟨c, hc, fun B hB => ?_⟩
  have hpos : 0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hB
    have h1 : Matrix.toEuclideanLin (P * B * Q) = 0 :=
      LinearMap.toContinuousLinearMap.injective (h0.trans (map_zero _).symm)
    exact Matrix.toEuclideanLin.injective (h1.trans (map_zero _).symm)
  unfold GlobalTheory.Count.dOp
  rw [Real.exp_log hpos]
  exact h B

theorem exp_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (K : ℝ) (h : ∀ v, Real.exp (d v) ≤ K) :
    Real.exp ((∑ v, d v) / Fintype.card ι) ≤ K := by
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max d
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : (∑ v, d v) / Fintype.card ι ≤ d v₀ := by
    rw [div_le_iff₀ hcard]
    calc ∑ v, d v ≤ ∑ _v : ι, d v₀ := Finset.sum_le_sum fun v _ => hv₀ v
      _ = d v₀ * Fintype.card ι := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact (Real.exp_le_exp.2 hmean).trans (h v₀)

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
  simp only [AutInst.f]
  omega

theorem inv_tau_mul_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 = 1) (K : ℝ)
    (h : ∀ v, Real.exp (GlobalTheory.Count.dOp (uMat (g.1 v))) ≤ K) :
    (GlobalTheory.Count.tau1 I (x * g))⁻¹ ≤ (GlobalTheory.Count.tau1 I x)⁻¹ * K := by
  have hK1 : g.2 ∈ I.Kset := by
    rw [hg]
    show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    simp only [OneMemClass.coe_one]
    exact one_mem _
  have hlog := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hK1
  have hx := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hxg := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hmean : Real.exp (GlobalTheory.Dec.dSum I g.1 / I.f) ≤ K := by
    have := exp_mean_le (fun v => GlobalTheory.Count.dOp (uMat (g.1 v))) K h
    rw [card_places] at this
    simpa only [GlobalTheory.Dec.dSum] using this
  have hdiv : GlobalTheory.Count.tau1 I x / GlobalTheory.Count.tau1 I (x * g) ≤ K := by
    rw [← Real.exp_log (div_pos hx hxg), Real.log_div hx.ne' hxg.ne']
    exact (Real.exp_le_exp.2 (by linarith)).trans hmean
  rw [inv_mul_eq_div, le_div_iff₀ hx, inv_mul_eq_div]
  exact hdiv

theorem sum_le_normInf {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) (τ : D.what₂.Tau) :
    ∑ i, ∑ j, ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ ≤ normInf θ V g := by
  unfold Formalism.L2.Theta.normInf
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun τ => ∑ i, ∑ j, (‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg _)

theorem uMat_ne_zero (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) (v : InfinitePlace I.F) : uMat (g.1 v) ≠ 0 := by
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact Units.ne_zero _

end GlobalTheory.TauNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRaStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_bounded_below_unipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA), I.IsIsot W → ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  first | exact @GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | exact GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | (intros; apply GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot <;> assumption)
end

