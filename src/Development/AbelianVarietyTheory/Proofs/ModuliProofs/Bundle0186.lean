module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PeriodObject

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun z i => ty i (a : E) * z i
      map_add' := fun z w => by funext i; simp [mul_add]
      map_smul' := fun c z => by funext i; simp [mul_left_comm] }
  map_one' := by ext z i; simp
  map_mul' a b := by
    ext z i
    show ty i ((a * b : 𝓞 E) : E) * _ = ty i (a : E) * (ty i (b : E) * _)
    push_cast
    rw [map_mul, _root_.mul_assoc]
  map_zero' := by ext z i; simp
  map_add' a b := by ext z i; simp [add_mul]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by simp [hermForm])
    (fun c z w => by simp [hermForm, smul_dotProduct])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun c z w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    {s : Set (Fin g → ℂ)} (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have e : (imForm Hm).comp (F.restrictScalars ℝ) = (imForm Hm).compl₂ (F'.restrictScalars ℝ) :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have im : ∀ z w, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im := fun z w =>
    LinearMap.congr_fun (LinearMap.congr_fun e z) w
  refine Complex.ext ?_ (im z w)
  have := im (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

theorem pelClass_of_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D o _ g k J b em w w' a bas ρ ty t D' f ν Q Hm hpq hw hρ hty hgen hζ hper hpol
    ⟨u, χ, hAH, hΛ, _, hpt, hF⟩ hprim
  have := t.ab.comm
  have hQ : ∀ (c : 𝓞 E) x, diagAct ty c (Q x) = Q (c • x) := fun c x => funext fun i => (hper.1 c x i).symm
  have hkeep : ∀ c, ∀ z ∈ u.Λ, diagAct ty c z ∈ u.Λ := fun c z hz => by
    obtain ⟨x, rfl⟩ := (hΛ z).1 hz
    exact (hΛ _).2 ⟨c • x, (hQ c x).symm⟩
  obtain ⟨act, hact⟩ := _root_.GlobalTheory.exists_oAct_of_map_lattice h₁ h₂ h₃ h₄ (𝓞 E) t.pol u (diagAct ty) hkeep
  change OAct (𝓞 E) t.A at act
  have hj : ∀ j, act.act (a j) = t.act j := fun j => by
    obtain ⟨F, hFQ, hFe⟩ := hF j
    have e : F.restrictScalars ℝ = (diagAct ty (a j)).restrictScalars ℝ :=
      LinearMap.ext_on_range hpol.2.2.1 fun x => (hFQ x).trans (hQ _ x).symm
    refine (_root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice h₁ h₂ h₃ h₄ t.pol t.pol t.L t.L u u (diagAct ty (a j)) (hkeep _)).unique
      ⟨act.hom _, hact _⟩ ⟨t.hom j, fun z => ?_⟩
    exact (congrArg u.ex (LinearMap.congr_fun e z).symm).trans (hFe z)
  have hadj : ∀ c, LBIso (cubeLB t.A ![fst t.A t.A ≫ act.act c, snd t.A t.A] t.L)
      (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ act.act (H.bar c)] t.L) := fun c => by
    refine (_root_.GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm h₁ h₂ h₃ h₄ t.pol u Hm χ _ _ _ _ hAH (act.hom c) (act.hom (H.bar c)) (hact c)
      (hact (H.bar c))).2 (hermForm_adjoint_of_span Hm (diagAct ty c) (diagAct ty (H.bar c)) hpol.2.2.1 ?_)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have e := D'.adj c x y
    rw [hQ, hQ, hpol.2.2.2.2.2, hpol.2.2.2.2.2, e]
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation h₁.globalFns E H _ t.A act t.L t.ab
    t.isLB (h₃ _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    rw [← hw, hj] at iso
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.2.2.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, act, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · show act.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hj, Category.comp_id, Category.id_comp]
  obtain ⟨σ, rfl⟩ : ∃ σ : ℂ →+* K, x = spMap σ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain rfl : σ.comp em = β :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_apply, hρ]
    exact _root_.GlobalTheory.detCond_of_diagonal_action h₁ h₂ h₃ h₄ E H D t.pol u Hm χ act ty hAH hty hact K σ
  obtain ⟨I, hI⟩ := _root_.GlobalTheory.exists_tateIso_of_periodMap_genus h₁ h₂ h₃ h₄ E H D D' f ν t.pol u Hm χ act Q hpq hgen hAH hpol.1 hΛ hpol.2.2.2.2.2
    (fun c n x => by
      rw [← hact, map_smul]
      exact congrArg (fun z => u.ex ((n : ℂ)⁻¹ • z)) (hQ c x).symm) K σ
  refine ⟨{ I with isom := fun n hn x y => weilIs_of_lbIso h₁.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn x y) },
    ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, hζ]
    exact (hI k hk).1
  · apply Over.OverMorphism.ext
    show (I.ev k _).left ≫ 𝟙 _ = spMap σ ≫ (t.pt i).left
    rw [Category.comp_id, hpt]
    exact (hI k hk).2 _

end GlobalTheory.PeriodObject
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.Coisotropic

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem isDominant_fst {X U V : Scheme.{0}} (j : U ⟶ X) (v : V ⟶ X) [IsDominant j] [IsOpenImmersion v] :
    IsDominant (pullback.fst v j) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst]
  exact j.denseRange.preimage v.isOpenEmbedding.isOpenMap

theorem section_ext {X U Y V : Scheme.{0}} {j : U ⟶ X} {q : Y ⟶ X} (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) [IsDominant j]
    [IsSeparated q] (v : V ⟶ X) [IsOpenImmersion v] {σ σ' : V ⟶ Y} (h : σ ≫ q = σ' ≫ q)
    (e : pullback.fst v j ≫ σ = pullback.fst v j ≫ σ') : σ = σ' := by
  have := isReduced_of_isNormalScheme hn
  have : IsReduced V := isReduced_of_isOpenImmersion v
  have := isDominant_fst j v
  exact ext_of_isDominant_of_isSeparated q h (pullback.fst v j) e

theorem extension_unique : ∀ (X U Y : Scheme.{0}) (j : U ⟶ X) (q : Y ⟶ X) (e : U ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsDominant j → IsSeparated q → ∀ (V V' T : Scheme.{0}) (v : V ⟶ X) (v' : V' ⟶ X), IsOpenImmersion v → IsOpenImmersion v' → ∀ (σ : V ⟶ Y) (σ' : V' ⟶ Y) (y : T ⟶ V) (y' : T ⟶ V'), y ≫ v = y' ≫ v' → σ ≫ q = v → σ' ≫ q = v' → pullback.fst v j ≫ σ = pullback.snd v j ≫ e → pullback.fst v' j ≫ σ' = pullback.snd v' j ≫ e → y ≫ σ = y' ≫ σ' := by
  intro X U Y j q e hn _ _ V V' T v v' _ _ σ σ' y y' hy e1 e2 e3 e4
  have key : pullback.fst v v' ≫ σ = pullback.snd v v' ≫ σ' := by
    refine section_ext (j := j) (q := q) hn (pullback.fst v v' ≫ v)
      (by rw [Category.assoc, Category.assoc, e1, e2, pullback.condition]) ?_
    have a := pullback.lift (pullback.fst (pullback.fst v v' ≫ v) j ≫ pullback.fst v v') _
      (by rw [Category.assoc]; exact pullback.condition) ≫= e3
    have b := pullback.lift (pullback.fst (pullback.fst v v' ≫ v) j ≫ pullback.snd v v') _
      (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition) ≫= e4
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at a b
    exact a.trans b.symm
  have := pullback.lift y y' hy ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem extension_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsDominant j → ∀ (V : Scheme.{0}) (v : V ⟶ X), IsOpenImmersion v → ∀ (a : D.La) (σ : Over.mk v ⟶ t.G), pullback.fst v j ≫ σ.left = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ → σ ^ l.A = 1 := by
  intro E _ _ _ H D l B _ b X U j s o t μ₀ hn _ V v _ a σ hσ
  have := t.semi.separated
  let hw := μ₀.cart.1.w
  have hmul : ∀ (T : Over U) (x y : T ⟶ o.t.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm
  have he : o.etaA a ^ l.A = 1 := by
    have h0 : o.etaA 0 = 1 := by simpa using o.etaA_ker 0
    have : ∀ n : ℕ, o.etaA (n • a) = o.etaA a ^ n := fun n => by
      induction n with
      | zero => simpa using h0
      | succ n ih => rw [succ_nsmul, o.etaA_add, ih, pow_succ]
    rw [← this, o.etaA_ker]
  let T : Over U := Over.mk (pullback.snd v j)
  let β := toBaseHom hmul T
  let ρ : Over.mk (T.hom ≫ j) ⟶ Over.mk v := Over.homMk (pullback.fst v j) pullback.condition
  have h1 : ρ ≫ σ = β (toUnit T ≫ o.etaA a) := by
    refine Over.OverMorphism.ext ?_
    have : (toUnit T).left = pullback.snd v j := (Category.comp_id _).symm.trans (Over.w (toUnit T))
    change pullback.fst v j ≫ σ.left = ((toUnit T).left ≫ (o.etaA a).left) ≫ μ₀.φ
    rw [this, hσ, Category.assoc]
  have h2 : ρ ≫ σ ^ l.A = ρ ≫ 1 := by
    rw [MonObj.comp_pow, h1, ← map_pow, ← MonObj.comp_pow, he, MonObj.comp_one, map_one, MonObj.comp_one]
  refine Over.OverMorphism.ext (section_ext (j := j) (q := t.G.hom) hn v ?_ (congrArg Over.Hom.left h2))
  rw [Over.w, Over.w]

theorem lattice_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧ Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  intro E _ _ _ H D
  have := D.fin
  exact ⟨datum_free_int D, Module.Finite.trans (𝓞 E) D.La, datum_finrank_int D⟩

end GlobalTheory.Coisotropic

theorem GlobalTheory.extends_of_orthogonal_to_extended : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (a : D.La), (∀ a', (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a').left ≫ μ₀.φ) → (l.A : ℤ) ∣ D.EF a a') → (∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ) := by
  intro hL _ hL3 E _ _ _ H D l B _ b X U _ j s o t μ₀ hn h1 h2 h3 h4 hA k _ _ x a ha
  have hk : ((l.A : ℕ) : k) ≠ 0 := by
    have := (hA.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  obtain ⟨hfr, hfi, hrk⟩ := GlobalTheory.Coisotropic.lattice_rank E H D
  have hg := GlobalTheory.smoothOfRelativeDimension_of_isPullback_isDominant X U _ _ j t.G.hom o.t.G.hom μ₀.φ _ μ₀.cart.1 h3 t.semi.smooth
    (GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l B b U s o).2.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one hL3 X t.G t.semi t.PP t.cub _ l.A k x hg hk
  let P := {p : Over.mk x ⟶ t.G // p ^ l.A = 1}
  let R : D.La → P → Prop := fun a p => ∃ (V : Scheme.{0}) (v : V ⟶ X) (_ : IsOpenImmersion v) (σ : V ⟶ t.G.left) (xV : Sp k ⟶ V), xV ≫ v = x ∧ σ ≫ t.G.hom = v ∧ pullback.fst v j ≫ σ = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ ∧ xV ≫ σ = p.1.left
  have hR : ∀ a p, R a p → ∃ (W : X.Opens) (σ : W.toScheme ⟶ t.G.left), Set.range x ⊆ W ∧ σ ≫ t.G.hom = W.ι ∧ pullback.fst W.ι j ≫ σ = pullback.snd W.ι j ≫ (o.etaA a).left ≫ μ₀.φ := by
    rintro a p ⟨V, v, hv, σ, xV, e1, e2, e3, -⟩
    refine ⟨v.opensRange, v.isoOpensRange.inv ≫ σ, ?_, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨xV z, by rw [← e1]; rfl⟩
    · rw [Category.assoc, e2, Scheme.Hom.isoOpensRange_inv_comp]
    · have hc : (pullback.fst v.opensRange.ι j ≫ v.isoOpensRange.inv) ≫ v = pullback.snd v.opensRange.ι j ≫ j := by
        rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, pullback.condition]
      have := pullback.lift _ _ hc ≫= e3
      rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
  have hcT : Nat.card (Subtype.val ⁻¹' T : Set P) = Nat.card T :=
    Nat.card_congr ⟨fun p => ⟨p.1.1, p.2⟩, fun τ => ⟨⟨τ.1, hT1 _ τ.2⟩, τ.2⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨p, hp⟩ := GlobalTheory.exists_rel_of_forall_dvd_of_card_mul D.La D.EF D.unimod l.A l.A_pos P (Subtype.val ⁻¹' T) R
    (by
      intro a c p h
      simpa only [R, o.etaA_add, o.etaA_ker, _root_.mul_one] using h)
    (by
      rintro a p p' ⟨V, v, hv, σ, xV, e1, e2, e3, e4⟩ ⟨V', v', hv', σ', xV', e1', e2', e3', e4'⟩
      refine Subtype.ext (Over.OverMorphism.ext ?_)
      rw [← e4, ← e4']
      exact GlobalTheory.Coisotropic.extension_unique X U _ j t.G.hom _ hn h3 t.semi.separated V V' _ v v' hv hv' σ σ' xV xV' (e1.trans e1'.symm)
        e2 e2' e3 e3')
    (fun p => GlobalTheory.TorsionSection.exists_section_extending_level E H D l B b X U j s o t μ₀ inferInstance hn h1 h2 h3 h4 hA k x p.1 p.2)
    (by rw [hcT, hrk]; exact hT3)
    (by
      rintro a p a' p' ⟨V, v, hv, σ, xV, e1, e2, e3, e4⟩ hp ⟨V', v', hv', σ', xV', e1', e2', e3', e4'⟩
      let w : pullback v v' ⟶ X := pullback.fst v v' ≫ v
      let τ : Over.mk w ⟶ t.G := Over.homMk (pullback.fst v v' ≫ σ) (by change (_ ≫ σ) ≫ _ = _ ≫ v; rw [Category.assoc, e2])
      let τ' : Over.mk w ⟶ t.G := Over.homMk (pullback.snd v v' ≫ σ') (by change (_ ≫ σ') ≫ _ = _ ≫ v; rw [Category.assoc, e2', pullback.condition])
      have key : ∀ {Z : Scheme.{0}} (z : Z ⟶ pullback v v') (u : Z ⟶ U), z ≫ w = u ≫ j →
          z ≫ τ.left = u ≫ (o.etaA a).left ≫ μ₀.φ ∧ z ≫ τ'.left = u ≫ (o.etaA a').left ≫ μ₀.φ := by
        intro Z z u hz
        constructor
        · have := pullback.lift (z ≫ pullback.fst v v') u (by rw [Category.assoc]; exact hz) ≫= e3
          rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
        · have := pullback.lift (z ≫ pullback.snd v v') u
            (by rw [Category.assoc, ← pullback.condition]; exact hz) ≫= e3'
          rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
      have hτ := GlobalTheory.Coisotropic.extension_pow E H D l B b X U j s o t μ₀ hn h3 _ w inferInstance a τ (key _ _ pullback.condition).1
      have hτ' := GlobalTheory.Coisotropic.extension_pow E H D l B b X U j s o t μ₀ hn h3 _ w inferInstance a' τ' (key _ _ pullback.condition).2
      obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil t.cub hτ hτ'
      let y : Sp k ⟶ pullback v v' := pullback.lift xV xV' (e1.trans e1'.symm)
      let ρ : Over.mk x ⟶ Over.mk w := Over.homMk y ((pullback.lift_fst_assoc _ _ _ _).trans e1)
      have r1 : ρ ≫ τ = p.1 := Over.OverMorphism.ext ((pullback.lift_fst_assoc _ _ _ _).trans e4)
      have r2 : ρ ≫ τ' = p'.1 := Over.OverMorphism.ext ((pullback.lift_snd_assoc _ _ _ _).trans e4')
      have hx := hζ.comp ρ
      rw [r1, r2] at hx
      have hx1 := congrArg Units.val (hx.unique (hT2 _ hp _ p'.2))
      obtain ⟨K, _, _, u, z, hz, hz1⟩ := GlobalTheory.exists_geometricPoint_rootOfUnity_eq_one_of_isDominant X U _ j w h3 inferInstance ζ.val l.A
        (by rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]) k y hk hx1
      let ρ' : Over.mk (u ≫ j) ⟶ Over.mk w := Over.homMk z hz
      have hu := hζ.comp ρ'
      have e : Units.map ρ'.left.appTop.hom.toMonoidHom ζ = 1 := Units.ext hz1
      rw [e] at hu
      exact GlobalTheory.Coisotropic.level_dvd_form_of_cubWeil_one hL E H D l B b X U j s o t μ₀ K u a a' _ _ (key z u hz).1 (key z u hz).2 hu)
    a (fun a' p' h => ha a' (hR a' p' h))
  exact hR a p hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := _root_.GlobalTheory.LevCover.levelCover_closed hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory


open LevelQuotRep in
theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact _root_.GlobalTheory.nonempty_objMap_of_finite_etale_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
end
end

