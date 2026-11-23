module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitive
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  have hax := (_root_.GlobalTheory.AbCoh.AxesPull.main R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (_root_.GlobalTheory.AbCoh.fp_ext_prod).2 R _ _ g g (_root_.GlobalTheory.AbCoh.globForm_FP R A g hA hs) (_root_.GlobalTheory.AbCoh.globForm_FP R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := _root_.GlobalTheory.AbCoh.globForm_FP R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add (f := _), map_add (f := _), h1, k2, h4, k5, add_zero, zero_add]
  have hbij := _root_.GlobalTheory.AbCoh.bijective_of_split_of_FP R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
section
noncomputable section

namespace GlobalTheory.LevelActionOfLifts

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => GlobalTheory.LevelActionLaws.eta_congr Xo (h a)
  unfold levR IsLevMove
  simp only [e]

def modHalf (l : Level H) (f : Dw.La →ₗ[𝓞 E] Dw.La) : Module.End (𝓞 E) (LaMod Dw l) :=
  Submodule.mapQ _ _ f (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

end General

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem actLev_of_lifts (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
    (h1 : ∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (hm : ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  let φ : G →* Module.End (𝓞 D.host.E) (LaMod Dw l) :=
    { toFun := fun g => modHalf l (lev g)
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (h1 a)
      map_mul' := fun g h => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (hm g h a) }
  let ψ : G →* (LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (𝓞 D.host.E) (LaMod Dw l)).toMonoidHom.comp φ.toHomUnits
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g y y' ↔
        levActR (Xo := Xo) (c := c) (GlobalTheory.FormTies.levFull Dw l) (ψ g) y y' := by
    intro g S _ _ y y'
    refine levR_congr (fun a => (Submodule.Quotient.eq _).1 ?_) y y'
    exact (liftLa_spec (ψ g) a).symm
  have L := GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨y', h⟩ := L.total (ψ g) S y
    exact ⟨y', (key g y y').2 h⟩
  · intro g S _ _ y y' y'' h h'
    exact L.func (ψ g) S y y' y'' ((key _ _ _).1 h) ((key _ _ _).1 h')
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g h S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat (ψ g) S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor (ψ g) S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

theorem actLev_of_lifts_of_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)), 1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → (∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  intro D H Dw l Xo c G _ lev hpq hA h1 hm
  exact actLev_of_lifts Xo c lev hpq (by rw [hA]; exact Nat.coprime_one_left _) h1 hm

end GlobalTheory.LevelActionOfLifts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
section
open NumberField MeasureTheory

namespace GlobalTheory.WeilM

theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  classical
  unfold GlobalTheory.ThetaSobolevBase.sumPure
  have hs : ∀ s : Finset (Fin n), MemLp (∑ i ∈ s, GlobalTheory.WeilM.pureA F (f i) (g i)) 2 μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)).add ih
  simpa using hs Finset.univ

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFramesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFramesD.symp_framesD | exact GlobalTheory.SympFramesD.symp_framesD | (intros; apply GlobalTheory.SympFramesD.symp_framesD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CInfAtSum
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory.CInfGlue

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_inv {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h0 : f y ≠ 0) :
    CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun v hv => hv.2, h₅.mono fun z hz => by simp only [hz]⟩
  have := h₅.self_of_nhds
  simp only at this
  rw [Set.mem_preimage, ← this]
  exact h0

theorem cInfAt_mul {f g : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h' : CInfAt g y) :
    CInfAt (fun z => f z * g z) y :=
  h.comp₂ h' (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sum {κ : Type} (s : Finset κ) (f : κ → CxPts p σ → ℝ) {y : CxPts p σ}
    (h : ∀ j ∈ s, CInfAt (f j) y) : CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem cInfAt_cut {χ v : CxPts p σ → ℝ} {O : Set (CxPts p σ)} (hχ : ∀ z, CInfAt χ z)
    (hs : tsupport χ ⊆ O) (hv : ∀ z ∈ O, CInfAt v z) (z : CxPts p σ) :
    CInfAt (fun w => χ w * v w) z := by
  by_cases hz : z ∈ O
  · exact cInfAt_mul (hχ z) (hv z hz)
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hs h)
    refine (cInfAt_const 0 z).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

theorem glue : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (T : Type) (m : T → CxPts p σ) (u : T → ℝ), (∀ x : CxPts p σ, ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧ ∀ t, m t ∈ O → v (m t) = u t) → ∃ v : CxPts p σ → ℝ, (∀ z, CInfAt v z) ∧ ∀ t, v (m t) = u t := by
  intro k _ X p hp σ T m u h
  haveI : CompactSpace (CxPts p σ) := GlobalTheory.CxPts.compactSpace σ hp
  choose O v hO hx hv hu using h
  choose χ hχ hχ0 hχx hχs using fun x => GlobalTheory.T.exists_smooth_bump_complexPoints_projective k X p hp σ x (O x) (hO x) (hx x)
  have hc : ∀ x, Continuous (χ x) := fun x =>
    continuous_iff_continuousAt.2 fun z => (hχ x z).continuousAt
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => {z | 0 < χ x z})
    (fun x => isOpen_lt continuous_const (hc x))
    (fun z _ => Set.mem_iUnion.2 ⟨z, hχx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ s, χ x z := fun z => by
    obtain ⟨x, hxs, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact Finset.sum_pos' (fun j _ => hχ0 j z) ⟨x, hxs, hz⟩
  refine ⟨fun z => (∑ x ∈ s, χ x z * v x z) * (∑ x ∈ s, χ x z)⁻¹, fun z => ?_, fun t => ?_⟩
  · exact cInfAt_mul
      (cInfAt_sum s (fun x w => χ x w * v x w) fun x _ => cInfAt_cut (hχ x) (hχs x) (hv x) z)
      (cInfAt_inv (cInfAt_sum s χ fun x _ => hχ x z) (hS z).ne')
  · have e : ∀ x ∈ s, χ x (m t) * v x (m t) = χ x (m t) * u t := fun x _ => by
      by_cases h0 : χ x (m t) = 0
      · simp [h0]
      · rw [hu x t (hχs x (subset_tsupport _ h0))]
    simp only
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, mul_right_comm, mul_inv_cancel₀ (hS _).ne', one_mul]

end GlobalTheory.CInfGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def blk (X : Data E r) (b : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun k a => b τ (Fin.castLE X.p0_le k) (Fin.castLE X.p0_le a)

theorem colP_rmul_eq (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    X.colP (rmul y b) τ a = ∑ k, blk X b τ k a • X.colP y τ k := by
  classical
  funext i
  have e1 : X.colP (rmul y b) τ a i = ∑ j, y τ i j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat y τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) i (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show blk X b τ c a * y τ i _ = _
    simp only [blk, Matrix.of_apply]
    rw [mul_comm]

theorem blk_det_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (blk X b τ).det ≠ 0 := by
  have hup : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular hup] at hd
  have hup' : (blk X b τ).BlockTriangular id := fun a c h => by
    simp only [blk, Matrix.of_apply]
    exact (hb τ).2 _ _ (by rw [Fin.lt_def]; simp only [Fin.val_castLE]; exact h)
  rw [Matrix.det_of_upperTriangular hup', Finset.prod_ne_zero_iff]
  intro k _
  rw [Finset.prod_ne_zero_iff] at hd
  exact hd _ (Finset.mem_univ _)

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gramPos_rmul (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul y b) τ = (blk X b τ)ᵀ * X.gramPos y τ * (blk X b τ).map (starRingEnd ℂ) := by
  ext a c
  rw [Data.gramPos_apply, colP_rmul_eq X y hb, colP_rmul_eq X y hb, hermC_sum_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Data.gramPos_apply,
    hermC_smul_left, hermC_sum_right, hermC_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem posPart_eq_dot (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.posPart y τ v = ((fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ⬝ᵥ
      ((X.gramPos y τ)⁻¹ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))))).re := by
  unfold Data.posPart
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]; rfl

theorem maj_rmul_any (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul y b) τ v = X.maj y τ v := by
  unfold Data.maj
  congr 2
  rw [posPart_eq_dot, posPart_eq_dot]
  set B := blk X b τ
  have hB := blk_det_ne X hb τ
  have hc : (fun a => hermC τ.1 X.Gm v (X.colP (rmul y b) τ a)) =
      (fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ᵥ* B.map (starRingEnd ℂ) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    simp only [vecMul, dotProduct, hermC_smul_right, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hw : (fun a => conj (hermC τ.1 X.Gm v (X.colP (rmul y b) τ a))) =
      Bᵀ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mulVec, dotProduct, hermC_smul_right, Matrix.transpose_apply, map_sum, map_mul,
      Complex.conj_conj]
    rfl
  have hB1 : IsUnit (B.map (starRingEnd ℂ)).det := by
    rw [show B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix B from rfl, ← RingHom.map_det]
    exact (Ne.isUnit hB).map _
  have hB2 : IsUnit Bᵀ.det := by rw [Matrix.det_transpose]; exact Ne.isUnit hB
  rw [hc, hw, gramPos_rmul X y hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB2, Matrix.mul_one]

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_mulVec' {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M *ᵥ v) = (M.map τ) *ᵥ Data.emb τ v := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Data.emb, Matrix.mulVec, dotProduct, map_sum]

theorem maj_le_four {r : ℕ} (X : DataX E r) {x : Frame X.Ψ r} (hx : IsOrth X.toData x) {ρ : ℝ}
    (hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {z z' : V (nd X.toData)}
    (hz : ‖z‖ ≤ ρ) (hz' : ‖z'‖ ≤ ρ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b) (v : Fin r → E) :
    ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) ≤
      4 * ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have hs : ∀ w : V (nd X.toData), ‖w‖ ≤ ρ → (r : ℝ) ^ 2 * ‖w‖ ≤ 1 / 100 := fun w hw =>
    (mul_le_mul_of_nonneg_left hw hr2).trans hρ
  have h1 := (_root_.GlobalTheory.ChartGraph.maj_cpt_le_two E r X.toData x z' hx (hs z' hz') τ
    (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v))).2
  have h2 := (_root_.GlobalTheory.ChartGraph.maj_cpt_le_two E r X.toData x z hx (hs z hz) τ (Data.emb τ.1 v)).1
  have e1 : X.maj (cpt X.toData x z') τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) =
      X.maj (cpt X.toData x z) τ (Data.emb τ.1 v) := by
    rw [← maj_rmul_any X.toData _ hb, ← heq, emb_mulVec',
      GlobalTheory.MajInv.maj_lact X.toData (X.Γ_stab γ hγ)]
  rw [e1] at h1
  linarith

end GlobalTheory.ChartMult

namespace GlobalTheory

open Matrix

theorem chart_mult_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  intro E _ _ _ r X x ε ρ hr hx hε hρ hL hmin
  classical
  have hdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X.toData hx
  obtain ⟨w, hwL, hli, hwB⟩ := exists_short_basis_at X x hdom ε hε hmin
  set Bd : ℝ := (2 * fdeg E * r : ℝ) ^ 4 * dE E ^ 2 / (4 * ε) with hBd
  have hd : 0 ≤ dE E := abs_nonneg _
  have hBd0 : 0 ≤ Bd := by positivity
  set T : Set (Fin r → E) := {v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ 4 * Bd} with hT
  have hTc := GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le E r X x ε (4 * Bd) hdom hε (by positivity) hmin
  have hTfin : T.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop] at hTc
    simp at hTc
  set Tf := hTfin.toFinset
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}
  let f : GL (Fin r) E → Fin r → Fin r → E := fun γ i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i
  have hmaps : Set.MapsTo f S (↑(Fintype.piFinset fun _ : Fin r => Tf)) := by
    rintro γ ⟨hγ, z, z', hz, hz', b, hb, heq⟩
    rw [Fintype.coe_piFinset]
    intro i _
    simp only [Tf, Set.Finite.coe_toFinset]
    refine ⟨hL γ hγ _ (hwL i), ?_⟩
    have := ChartMult.maj_le_four X hx hρ hγ hz hz' hb heq (w i)
    have := hwB i
    show ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w i)) ≤ 4 * Bd
    linarith
  have hinj : Set.InjOn f S := by
    intro γ _ γ' _ h
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let bw := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hlin : Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E) = Matrix.toLin' (γ' : Matrix (Fin r) (Fin r) E) :=
      bw.ext fun i => by
        simp only [bw, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.toLin'_apply]
        exact congrFun h i
    exact Units.ext (Matrix.toLin'.injective hlin)
  have hS := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_coe_eq_coe_finsetCard, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hS
  have hTe : T.encard = (Tf.card : ℕ∞) := hTfin.encard_eq_coe_toFinset_card
  rw [hTe, ENat.toENNReal_coe] at hTc
  set a : ℝ := (1 + 2 * Real.sqrt (4 * Bd / ε)) ^ (2 * fdeg E * r) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsq : Real.sqrt (4 * Bd / ε) = 2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε := by
    rw [show 4 * Bd / ε = (2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε) ^ 2 by
      rw [hBd]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hmult : a ^ r = multBd E r ε := by
    rw [ha, hsq, multBd, ← pow_mul]
    congr 1
    · ring
    · ring
  calc (S.encard : ℝ≥0∞) ≤ ((Tf.card ^ r : ℕ) : ℕ∞) := ENat.toENNReal_le.mpr hS
    _ = (Tf.card : ℝ≥0∞) ^ r := by rw [ENat.toENNReal_coe]; push_cast; rfl
    _ ≤ ENNReal.ofReal a ^ r := pow_le_pow_left₀ zero_le hTc r
    _ = ENNReal.ofReal (multBd E r ε) := by rw [← ENNReal.ofReal_pow ha0, hmult]

end GlobalTheory
end

