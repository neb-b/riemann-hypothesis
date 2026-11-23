module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleFinrankOne.IrrOfFinrankOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSet
section
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory

theorem absIrrChar_comp_mem_gxIrrSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K]
    [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ →
    (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  intro G _ _ K _ _ σ χ h
  classical
  obtain ⟨⟨n, ρc, htr⟩, hip⟩ := PI.XgCTieBrWork.Chars.absIrr_isIrr σ h
  have htr' : ∀ x, σ (χ x) = Matrix.trace ((ρc x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := htr
  have hchar : ∀ x, (PI.XgCTieBrWork.Chars.ofGL ρc).character x = σ (χ x) := fun x => by
    rw [PI.XgCTieBrWork.Chars.char_ofGL, htr']
  haveI : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have hfr := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (PI.XgCTieBrWork.Chars.ofGL ρc) (PI.XgCTieBrWork.Chars.ofGL ρc)
  have hsum : ∑ g : G, (PI.XgCTieBrWork.Chars.ofGL ρc).character g *
      (PI.XgCTieBrWork.Chars.ofGL ρc).character g⁻¹ = (Nat.card G : ℂ) := by
    simp_rw [hchar]
    rw [Nat.card_eq_fintype_card, ← hip]
    unfold Formalism.L2.NT.ipG
    refine Finset.sum_congr rfl fun x _ => ?_
    show σ (χ x) * σ (χ x⁻¹) = σ (χ x) * star (σ (χ x))
    rw [htr' x, htr' x⁻¹, PI.XgCTieBrWork.Chars.star_trace_inv]
  rw [hsum, inv_mul_cancel₀ (NeZero.ne _)] at hfr
  have h1 : Module.finrank ℂ (Representation.IntertwiningMap (PI.XgCTieBrWork.Chars.ofGL ρc)
      (PI.XgCTieBrWork.Chars.ofGL ρc)) = 1 := by
    exact_mod_cast hfr.symm
  exact ⟨n, PI.XgCTieBrWork.Chars.ofGL ρc, PI.XgCTieBrWork.Chars.irr_of_finrank_one _ h1, funext hchar⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQpStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), Per.φB l b = b → C.ι b ∈ Per.FilD l 0 → ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  first | exact @GlobalTheory.MemLoc.fundamental_exact | exact GlobalTheory.MemLoc.fundamental_exact | (intros; apply GlobalTheory.MemLoc.fundamental_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJointStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  first | exact @GlobalTheory.TameJoint.exists_pow_joint | exact GlobalTheory.TameJoint.exists_pow_joint | (intros; apply GlobalTheory.TameJoint.exists_pow_joint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleRigidifiedSquareIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigSq

variable {X Y : Scheme.{0}}

theorem gm_sq_g (L : LB X) (f : Y ⟶ X) (y : Y) (j j' : L.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ 2 := by
  have hp : f y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).U (fun _ => j') :=
    ⟨Set.mem_iInter.2 fun _ => hj, Set.mem_iInter.2 fun _ => hj'⟩
  show gm f y _ (∏ _k : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (2 : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow]
  refine (congrArg (· ^ (2 : ℤ)) ((gm_res f y _ hp _).trans (gm_pull f (𝟙 X) y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _))).trans ?_
  rw [Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_rig {S : Scheme.{0}} {G : Over S} [GrpObj G] (R : RigLB G) (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y)
    (j j' : R.L.ι) (hj : eSec G (f y) ∈ R.L.U j) (hj' : eSec G (f y) ∈ R.L.U j') :
    gm f y _ (R.rig.s (fun _ => j)) = gm (f ≫ eSec G) y _ (R.L.g j j') * gm f y _ (R.rig.s (fun _ => j')) := by
  have hp : f y ∈ (R.L.pull (eSec G)).U (fun _ => j) ⊓ (R.L.pull (eSec G)).U (fun _ => j') :=
    ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm f y _) (R.rigGen (fun _ => j) (fun _ => j'))
  rw [gm_res f y _ hp, map_mul, gm_res f y _ hp] at e
  refine e.trans (congrArg (· * _) ?_)
  show gm f y _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (R.L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f (eSec G) y (R.L.U j ⊓ R.L.U j') ⟨hj, hj'⟩ _)

theorem eSec_comp_toUnit {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ (toUnit G).left = 𝟙 _ := by
  rw [eSec, ← Over.comp_left, show η[G] ≫ toUnit G = 𝟙 _ from toUnit_unique _ _]
  rfl

end GlobalTheory.RigSq

namespace GlobalTheory.RigSq

theorem exists_rescale : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  intro S G _ L L' w hw
  have hπ := eSec_comp_toUnit G
  let W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens := fun p =>
    (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)
  have hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) :=
    fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩
  let q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ := fun p =>
    res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
      (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹
  have hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p →
      gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
        (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹ := by
    intro Y f y p hy
    simp only [q, map_mul, map_pow, map_inv]
    rw [gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]
    rfl
  obtain ⟨u, hu⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart L.isLB (eSec G x)
      obtain ⟨i', hi'⟩ := exists_chart L'.isLB (eSec G x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by
      rw [hq _ x p hx.1, hq _ x p' hx.2]
      have h1 : eSec G x ∈ L.L.U p.1 := mem_pull.1 hx.1.1
      have h2 : eSec G x ∈ L'.L.U p.2 := mem_pull.1 hx.1.2
      have h1' : eSec G x ∈ L.L.U p'.1 := mem_pull.1 hx.2.1
      have h2' : eSec G x ∈ L'.L.U p'.2 := mem_pull.1 hx.2.2
      rw [gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2',
        gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2)
          (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1')
          (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ => h2'),
        gm_sq_g L.L (𝟙 _ ≫ eSec G) x p.1 p'.1 h1 h1', gm_sq_g L'.L (𝟙 _ ≫ eSec G) x p.2 p'.2 h2 h2']
      generalize gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A
      generalize gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B
      generalize gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C
      generalize gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D
      generalize gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
  have hT : ∀ p, (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ :=
    fun _ _ _ => trivial
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)),
      ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) :=
    ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩
  refine ⟨w', ?_, ?_⟩
  · intro p p'
    rw [hw', hw']
    apply unit_ext
    intro x hx
    have e := congrArg (gm (𝟙 G.left) x _) (hw p p')
    rw [gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx] at e
    simp only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]
    rw [e, _root_.mul_assoc]
  · intro Z r z jL jL' h1 h2
    have hy : r z ∈ W (jL, jL') := ⟨mem_pull.2 h1, mem_pull.2 h2⟩
    have hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') :=
      hWle (jL, jL') hy
    have hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') =
        gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u := by
      show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _
      erw [hw' (fun _ => jL, fun _ => jL')]
      rw [map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ,
        Category.comp_id]
      rfl
    rw [hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]
    generalize gm r z _ (L.rig.s (fun _ => jL)) = A
    generalize gm r z _ (L'.rig.s (fun _ => jL')) = B
    generalize gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end GlobalTheory.RigSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
section
noncomputable section

namespace GlobalTheory.SqLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

abbrev sq (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {x : X} {j : L.ι} (h : x ∈ L.U j) : x ∈ (sq L).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => h

theorem gm_sq_g (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by
  refine (gm_linComb L (fun _ => 𝟙 X) (fun _ => 2) f y _ _ (mem_sq hj) (mem_sq hj')).trans ?_
  rw [Fintype.prod_unique, Category.comp_id]

def gq (w : LB.Iso (sq L') ((sq L).pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gw w f y (fun _ => j) (fun _ => k)

theorem gq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (f : Y ⟶ X') (y : Y) {j j' : L.ι} {k k' : L'.ι}
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gq w f y j k = gm (f ≫ F) y _ (L.g j j') ^ (2 : ℤ) * (gm f y _ (L'.g k k') ^ (2 : ℤ))⁻¹ * gq w f y j' k' := by
  rw [gq, gq, hw Y f y _ _ _ _ (mem_sq hj) (mem_sq hj') (mem_sq hk) (mem_sq hk'), gm_sq_g (f ≫ F) y hj hj',
    gm_sq_g f y hk hk']

def pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι)
    (q : K → L'.ι) : (Z.presheaf.stalk z)ˣ := ∏ k, gq w (r ≫ φ' k) z (p k) (q k) ^ ε k

theorem trF_two {M : LB X} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → M.ι) :
    trF φ (fun k => 2 * ε k) r z j j' = trF φ ε r z j j' ^ (2 : ℤ) := by
  rw [trF, trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

theorem pq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by
  rw [trF_two, trF_two, pq, pq, trF, trF, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gq_trans hw (r ≫ φ' k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  rw [smul_add, smul_add, smul_comm (ε k) (2 : ℤ), smul_neg, smul_comm (ε k) (2 : ℤ)]

theorem exists_pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pq w φ' ε r z p q := by
  have le : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ (((sq L).pull F).U (fun _ => fun _ => p k) ⊓ (sq L').U (fun _ => q k)) := fun k y hy =>
    ⟨mem_pull.2 (mem_sq (Set.mem_iInter.1 hy.1 k)), mem_sq (Set.mem_iInter.1 hy.2 k)⟩
  exact ⟨∏ k, res (le k) (pullU (φ' k) _ (w.s (fun _ => fun _ => p k, fun _ => q k))) ^ ε k, fun Z r z hz =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
      ((gm_res r z (le k) hz _).trans (gm_pull r (φ' k) z _ (le k hz) _))))⟩

theorem exists_sq_up {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
  choose u hu using fun p q => exists_pq w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ (u p q * res inf_le_right (a.s q) ^ 2) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 :=
      fun Z r z q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu p q Z r z hz)
        ((map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hz _))))
    obtain ⟨s, hs⟩ := glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_left)
      (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) (fun q => u p q * res inf_le_right (a.s q) ^ 2)
      (fun q q' y hy => by
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pq_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ _ (𝟙 Y) y hy.1.1, trF_two, gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
        abel)
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (hs j _ (𝟙 Y) y q hj m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hj' m)).symm)
  rw [pq_trans hw φ' ε (𝟙 Y) y hj hj' m m, trF_self hL' _ _ (𝟙 Y) y m, inv_one, _root_.mul_one, _root_.mul_assoc]

theorem exists_sq_gen : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  intro X X' Y L L' F hL hL' w hwg K _ φ' ε a ha
  obtain ⟨t, ht, hv⟩ := exists_sq_up ((isGen_iff w).1 hwg) hL hL' a ha
  refine ⟨t, ht, fun Z z ψ J J' => ∏ k, gq w (ψ k) z (J (ψ k ≫ F)) (J' (ψ k)) ^ ε k, fun Z r z J J' hJ hJ' => ?_⟩
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  simp only [pq, Category.assoc]
  rfl

end GlobalTheory.SqLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldsIsConductorPrimesModulus
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlatten
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linComb_pow_pow_sec {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ) (hm : m = a * n) (g : Y ⟶ X)
    (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι),
      g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  let M := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)
  let N := LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => n)
  let P := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)
  have le : ∀ i : Fin 1 → L.ι, P.U i ≤ N.U (fun k _ => i k) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k
  have gN : ∀ (x : Y) (i j : Fin 1 → L.ι) (hi : x ∈ P.U i) (hj : x ∈ P.U j),
      gm (𝟙 Y) x (P.U i ⊓ P.U j) (P.g i j) =
        gm (𝟙 Y) x (N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k)) (N.g (fun k _ => i k) (fun k _ => j k)) := by
    intro x i j hi hj
    refine (gm_linComb L (fun _ : Fin 1 => g) (fun _ => m) (𝟙 Y) x i j hi hj).trans
      (Eq.trans ?_ (gm_linComb M (fun _ : Fin 1 => g) (fun _ => n) (𝟙 Y) x _ _ (le i hi) (le j hj)).symm)
    simp only [Fintype.prod_unique]
    refine Eq.trans ?_ (congrArg (· ^ n) (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => a) (𝟙 Y ≫ g) x
      (fun _ => i default) (fun _ => j default) (Set.mem_iInter.1 (le i hi) default)
      (Set.mem_iInter.1 (le j hj) default))).symm
    simp only [Fintype.prod_unique, Category.comp_id, hm, zpow_mul]
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (fun k _ => i k)), fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro x hx
    have hx' : (𝟙 Y) x ∈ P.U i ⊓ P.U j := hx
    have hN : (𝟙 Y) x ∈ N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k) := ⟨le i hx.1, le j hx.2⟩
    have e := congrArg (gs (𝟙 Y) x _) (s.compat (fun k _ => i k) (fun k _ => j k))
    rw [gs_res _ _ _ hN, gs_mul _ _ _ hN, gs_unit _ _ _ hN, gs_res _ _ _ hN] at e
    have hi : (𝟙 Y) x ∈ P.U i := hx.1
    have hj : (𝟙 Y) x ∈ P.U j := hx.2
    rw [gs_res _ _ _ hx', gs_res (𝟙 Y) x (le i) hi, gs_mul _ _ _ hx', gs_unit _ _ _ hx', gs_res _ _ _ hx',
      gs_res (𝟙 Y) x (le j) hj, e, gN x i j hx.1 hx.2]
  · intro Z r z j hj
    have hz : r z ∈ P.U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
    exact gs_res r z (le _) hz _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflatten
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPowUnflat

theorem unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  intro X Y L a n m hm g s'
  have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
      LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
        LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
  refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
  · refine fn_ext fun y hy => ?_
    have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
    have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
    have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
    have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
    rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
    erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
    erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
      gs_res (𝟙 Y) y _ hy.2, c]
    erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
    have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
      simpa using Set.mem_iInter.1 hy.1 0
    have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
      simpa using Set.mem_iInter.1 hy.2 0
    simp only [Fin.prod_univ_one]
    erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
    simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
    rfl
  · intro Z r z j h
    exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm

end GlobalTheory.SecPowUnflat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WtsOkAndSizes
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem wts_ok_and_sizes :
    ∀ (B : Base) (X : PreX B.toPre), B.wts.Ok ∧ Sizes (B.primes X) B.wts X.a :=
  fun B X => ⟨B.wts_isOk, B.primes_sizes X⟩

end GlobalTheory.Mem
end

