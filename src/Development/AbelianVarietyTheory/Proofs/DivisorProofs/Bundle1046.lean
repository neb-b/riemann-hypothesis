module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemSpanFormsOfMulMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorsCommonEigenvalueInertPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertEig


open Classical in
noncomputable def coeff (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ) (b : List ℕ → ℂ) (d : List ℤ) : ℂ :=
  if h : ∃ s, ok s ∧ lab n s = d then b h.choose else 0

theorem coeff_cases {H : Type} [AddCommGroup H] [Module ℂ H] (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ)
    (isLab : List ℤ → Prop) (hL : ∀ d, isLab d → ∃ s, ok s ∧ lab n s = d) (b : List ℕ → ℂ)
    (ops : List ℤ → Module.End ℂ H) (x : H) (hx : ∀ s, ok s → ops (lab n s) x = b s • x) (d : List ℤ) :
    (¬ isLab d ∧ coeff n ok lab b d = 0) ∨ ops d x = coeff n ok lab b d • x := by
  classical
  by_cases h : ∃ s, ok s ∧ lab n s = d
  · right
    have hf : coeff n ok lab b d = b h.choose := dif_pos h
    have h1 := hx _ h.choose_spec.1
    rw [h.choose_spec.2] at h1
    rw [hf]
    exact h1
  · left
    exact ⟨fun hl => h (hL d hl), dif_neg h⟩

theorem eig_of_single {H Γ ι W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (rep : List ℤ → Finset ι) (act : Γ → ι → Γ)
    (ops : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hops : ∀ c x, e (ops c x) = fun g => c.sum fun d z => z • ∑ γ ∈ rep d, e x (act g γ))
    (f : List ℤ → ℂ) (x : H) (hx : ∀ d, (rep d = ∅ ∧ f d = 0) ∨ ops (Finsupp.single d 1) x = f d • x)
    (c : List ℤ →₀ ℂ) : ops c x = (c.sum fun d z => z * f d) • x := by
  have hd : ∀ d g, ∑ γ ∈ rep d, e x (act g γ) = f d • e x g := by
    intro d g
    rcases hx d with ⟨h0, hf⟩ | h1
    · rw [h0, hf, Finset.sum_empty, zero_smul]
    · have h2 := congrFun (hops (Finsupp.single d 1) x) g
      rw [h1, map_smul, Finsupp.sum_single_index (by simp), one_smul] at h2
      exact h2.symm
  apply he
  rw [hops c x, map_smul]
  funext g
  simp only [Pi.smul_apply, Finsupp.sum, hd, smul_smul, Finset.sum_smul]

theorem labIn_eq (n : ℕ) (s : List ℕ) : GlobalTheory.Hk3.labIn n s = labIn n s := rfl


set_option maxHeartbeats 1000000 in
theorem veig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM j t hV hOps P hP hc b y y' hb cV
  have hL : ∀ d, IsLab (Vc D j) P d → ∃ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s ∧ labIn (Vc D j).rank s = d := by
    intro d hl
    obtain ⟨h1, h2, h3⟩ := (_root_.GlobalTheory.LabChar.labels_char (Vc D j) P d).1 hl
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (_root_.GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨h1, h2, h3 hc⟩
    exact ⟨s, ⟨hs2, hs3, hs1⟩, (labIn_eq _ _).symm.trans hs4.symm⟩
  have hrep : ∀ d, ¬ IsLab (Vc D j) P d → GlobalTheory.Hk3.rep (Vc D j) P d = ∅ := by
    intro d hd
    classical
    exact dif_neg hd
  have key : ∀ x : (R.HV j t).H, (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s →
      hV P (Finsupp.single (labIn (Vc D j).rank s) 1) x = b s • x) →
      hV P cV x = (cV.sum fun d z => z * coeff (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn b d) • x := by
    intro x hx
    refine eig_of_single (R.HV j t).e (hM.HV j t).1 (GlobalTheory.Hk3.rep (Vc D j) P) (fun g γ => g * (finHom (Vc D j)).rangeRestrict γ)
      (hV P) (fun c x => hOps P hP c x) _ x ?_ cV
    intro d
    rcases coeff_cases (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn (IsLab (Vc D j) P) hL b
      (fun d => hV P (Finsupp.single d 1)) x hx d with ⟨h0, hf⟩ | h1
    · exact Or.inl ⟨hrep d h0, hf⟩
    · exact Or.inr h1
  exact ⟨_, key y (fun s hs => (hb s hs).1), key y' (fun s hs => (hb s hs).2)⟩

end GlobalTheory.InertEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem zc_eq_scL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    zc E N = lie E N (Central.scL N 1) := by
  unfold zc
  congr 1

theorem splitCentre_eq_scalar {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (t : ℝ) :
    splitCentre E N t = Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E)))) := by
  have e : (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) := by
    funext w; simp
  unfold splitCentre
  rw [e]
  exact cornerGL_scalar _ _

theorem zc_comm_mem_eigen : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ N
  rw [zc_eq_scL]
  refine ⟨fun o => (Central.lie_act 1 o).eq, Central.lie_mem_Zalg 1, fun φ c => ⟨fun h t g => ?_, fun h => ?_⟩⟩
  · have e : Central.scL N (t • (1 : Cinf E)) = t • Central.scL N (1 : Cinf E) := by
      funext i j
      change Matrix.diagonal (fun _ => t • (1 : Cinf E)) i j = t • Matrix.diagonal (fun _ => (1 : Cinf E)) i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h1 : lie E N (Central.scL N (t • (1 : Cinf E))) φ = (c * t) • φ := by
      rw [e, map_smul, LinearMap.smul_apply, h, mul_comm, mul_smul, Complex.coe_smul]
    have h2 := congrFun (congrArg Subtype.val (Central.rs_exp _ _ φ h1)) g
    rw [splitCentre_eq_scalar, scalar_comm]
    exact h2
  · refine Subtype.ext <| funext fun g => ?_
    have h1 := Central.hasDerivAt_scalar (1 : Cinf E) φ g
    have e : ∀ t : ℝ, φ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin N) (infId E (expU (t • (1 : Cinf E))))) =
        Complex.exp (c * t) * φ.1 g := fun t => by rw [← scalar_comm, ← splitCentre_eq_scalar, h]
    simp only [e] at h1
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t) * φ.1 g) (c * φ.1 g) 0 := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul c).cexp).mul_const (φ.1 g)
    exact h1.unique h2

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultipleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  first | exact @GlobalTheory.SplitLatMatch.lat_split | exact GlobalTheory.SplitLatMatch.lat_split | (intros; apply GlobalTheory.SplitLatMatch.lat_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem torsion_exhaust_geometric : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  intro hL R _ _ _ P N hN1 hNu C b hb hgen K _ _ x p hp
  have hNu' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hNu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨hfin, -, -, het, hcard⟩ := hL.mulN (Spec (CommRingCat.of R)) P N hN1
  have : Etale (mulA P.A N).left := het hNu'
  have : IsSeparated (mulA P.A N).left := inferInstance
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ≫ mulA P.A N = y ^ N := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of R))}, (1 : Z ⟶ P.A).left = Z.hom ≫ η[P.A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let Kk : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (mulA P.A N).left η[P.A].left)
  have hη : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  let i : Kk ⟶ P.A := Over.homMk (pullback.fst (mulA P.A N).left η[P.A].left) (by
    change pullback.fst (mulA P.A N).left η[P.A].left ≫ P.A.hom = pullback.snd (mulA P.A N).left η[P.A].left
    rw [← Over.w (mulA P.A N), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hlift : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ^ N = 1 → ∃ l : Z ⟶ Kk, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA P.A N).left = Z.hom ≫ η[P.A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over (Spec (CommRingCat.of R))} (l l' : Z ⟶ Kk), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  have : Etale Kk.hom := inferInstanceAs (Etale (pullback.snd (mulA P.A N).left η[P.A].left))
  have : IsSeparated Kk.hom := inferInstanceAs (IsSeparated (pullback.snd (mulA P.A N).left η[P.A].left))

  have inj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
      (σ τ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A), σ ^ N = 1 → τ ^ N = 1 →
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ τ → σ = τ := by
    intro F _ y σ τ hσ hτ e
    obtain ⟨ls, rfl⟩ := hlift σ hσ
    obtain ⟨lt, rfl⟩ := hlift τ hτ
    have e' : toUnit (Over.mk y) ≫ ls = toUnit (Over.mk y) ≫ lt := hmono _ _ (by simpa using e)
    have hu : (toUnit (Over.mk y)).left = y := by
      simpa using Over.w (toUnit (Over.mk y))
    have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of R)))
    have key : ls.left = lt.left := by
      refine GlobalTheory.eq_of_connected_of_unramified_of_point Kk.hom
        ((Over.w ls).trans (Over.w lt).symm) y ?_
      have h2 := congr(($e').left)
      rw [Over.comp_left, Over.comp_left, hu] at h2
      exact h2
    rw [Over.OverMorphism.ext key]
  have natK : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), (N : F) ≠ 0 :=
    fun y => by simpa using (hNu.map (Spec.preimage y).hom).ne_zero
  let T0 := {σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A // σ ∈ Set.range b}
  have tor : ∀ σ : T0, σ.1 ^ N = 1 := fun σ => by obtain ⟨c, hc⟩ := σ.2; rw [← hc]; exact hb c
  let res : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      T0 → {q : Over.mk y ⟶ P.A // q ^ N = 1} := fun y σ =>
    ⟨toUnit _ ≫ σ.1, by rw [← MonObj.comp_pow, tor σ, MonObj.comp_one]⟩
  have resInj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      Function.Injective (res y) := fun y σ τ e =>
    Subtype.ext (inj y σ.1 τ.1 (tor σ) (tor τ) (congrArg Subtype.val e))
  let Ω := AlgebraicClosure (FractionRing R)
  have c0 := hcard Ω (TF (R := R) Ω).hom (natK (TF (R := R) Ω).hom)
  have cx := hcard K x (natK x)
  have hpos : N ^ (2 * P.g) ≠ 0 := pow_ne_zero _ (by omega)
  have : Finite {q : Over.mk (TF (R := R) Ω).hom ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (c0 ▸ hpos)
  have : Finite {q : Over.mk x ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (cx ▸ hpos)
  have bij0 : Function.Bijective (res (TF (R := R) Ω).hom) := by
    refine ⟨resInj _, fun q => ?_⟩
    obtain ⟨c, hc⟩ := hgen q.1 q.2
    exact ⟨⟨b c, c, rfl⟩, Subtype.ext hc.symm⟩
  have cT : Nat.card T0 = N ^ (2 * P.g) := (Nat.card_eq_of_bijective _ bij0).trans c0
  have bijx := (Nat.bijective_iff_injective_and_card (res x)).2 ⟨resInj x, cT.trans cx.symm⟩
  obtain ⟨⟨σ, c, rfl⟩, hσ⟩ := bijx.2 ⟨p, hp⟩
  exact ⟨c, (congrArg Subtype.val hσ).symm⟩

end GlobalTheory.Poinc.Tors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
section
open NumberField IsDedekindDomain GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

open MvPolynomial

namespace GlobalTheory.NablaFin

theorem totalDegree_le_of_colW {O : Type} [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ weightedHomogeneousSubmodule O (Formalism.GradedWeylDivisibility.colW N N) ν) :
    f.totalDegree ≤ ∑ t, ν t := by
  rw [mem_weightedHomogeneousSubmodule] at hf
  unfold totalDegree
  refine Finset.sup_le fun s hs => ?_
  have hw := hf (mem_support_iff.1 hs)
  rw [← hw, Finsupp.weight_apply]
  refine le_of_eq ?_
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem dualWeyl_finite (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ν : Fin N → ℕ) :
    Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := by
  have hle : Formalism.GradedWeylDivisibility.dualWeyl O N N ν ≤ restrictTotalDegree (Fin N × Fin N) O (∑ t, ν t) := by
    intro f hf
    rw [mem_restrictTotalDegree]
    exact totalDegree_le_of_colW N ν f (by unfold Formalism.GradedWeylDivisibility.dualWeyl at hf; exact hf.1)
  haveI : IsNoetherian O (Formalism.GradedWeylDivisibility.dualWeyl O N N ν) := isNoetherian_of_le hle
  infer_instance

theorem nablaT_finite : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (N : ℕ) (ι : Type) [Fintype ι]
    (lam : ι → ℕ → ℕ), Module.Finite O (NablaT O N lam) := by
  intro O _ _ N ι _ lam
  haveI : ∀ τ, Module.Finite O (Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ))) := fun τ => dualWeyl_finite O N _
  exact PiTensorProduct.finite

end GlobalTheory.NablaFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace

theorem adele_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  intro F E _ _ _ _ _ σ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]
  · have htm : ∀ (a : AF F) (e : E), Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] e) =
        a * algebraMap F (AF F) (Algebra.trace F E e) := by
      intro a e
      have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; abel
    | tmul a e =>
      rw [htm, Algebra.TensorProduct.algebraMap_apply, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        ← TensorProduct.tmul_add, ← trace_eq h, mul_comm, ← Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CMTrace
end
end

