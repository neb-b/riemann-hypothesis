module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.Bundle0003
public import GroundTheory.GlobalFields.TateThesis.TateMain
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenImmersionChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchExponentEqZeroOfMulSelf
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

theorem archExponent_eq_zero_of_mul_self {K : Type _} [Field K] [NumberField K]
    (w : InfinitePlace K) {μ : GroundTheory.Global.HeckeCharacter K} (hμ : μ * μ = 1) :
    archExponent w μ = 0 := by
  have h : archExponent w μ = -archExponent w μ := by
    rw [← archExponent_inv, ← eq_inv_of_mul_eq_one_left hμ]
  linarith

end GlobalTheory.CompanionTheory.EisRk1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.LinRedFactor

open GlobalTheory.LinRed

variable {n : ℕ}

theorem isCompact_unitary_fin :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := _) hc ?_ ?_
  · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

theorem unitary_mul_star {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hU

theorem star_mul_unitary {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 hU

theorem conj_mul_conj {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (s t : Matrix (Fin n) (Fin n) ℂ) :
    (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * (s * t) * U := by
  calc (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * s * (U * Uᴴ) * t * U := by
        simp only [Matrix.mul_assoc]
    _ = Uᴴ * (s * t) * U := by
        rw [unitary_mul_star hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem tri_mul {U s t : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hs : (Uᴴ * s * U).BlockTriangular id) (ht : (Uᴴ * t * U).BlockTriangular id) :
    (Uᴴ * (s * t) * U).BlockTriangular id := by
  rw [← conj_mul_conj hU]
  exact hs.mul ht

theorem isClosed_tri (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {s : Matrix (Fin n) (Fin n) ℂ | (Uᴴ * s * U).BlockTriangular id} := by
  simp only [Matrix.BlockTriangular, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
    continuous_const

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) :
    IsCompact (maxCpt G) := by
  refine isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx
  exact ⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU))
    (closure_mono Set.inter_subset_left hx), hxU⟩

def Good (G : Set (Matrix (Fin n) (Fin n) ℂ)) (U g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

theorem good_nhds {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → Good G U g)
    {g₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : Good G U g₀) :
    ∀ᶠ g in 𝓝 g₀, g ∈ G → Good G U g := by
  obtain ⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩ := h₀
  have hkk : k₀ * k₀ᴴ = 1 := unitary_mul_star hk₀.2
  have hkk' : k₀ᴴ * k₀ = 1 := star_mul_unitary hk₀.2
  have hsu : IsUnit s₀ := hG.isUnit s₀ hs₀
  have hss : s₀ * s₀⁻¹ = 1 := Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hss' : s₀⁻¹ * s₀ = 1 := Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1 := by
    rw [← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]
  have ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1) := by
    have := hφ.tendsto (k₀ * s₀)
    rwa [e] at this
  filter_upwards [ht.eventually h] with g hg hgG
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩ :=
    hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))
  refine ⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀,
    hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩
  calc g = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by
        calc g = (k₀ * k₀ᴴ) * g * (s₀⁻¹ * s₀) := by
              rw [hkk, hss', Matrix.one_mul, Matrix.mul_one]
          _ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]
    _ = k₀ * k₁ * (s₁ * s₀) := by
        rw [e₁]; simp only [Matrix.mul_assoc]

theorem isClosed_factor {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ |
      ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  have hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ |
      (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id} :=
    (isClosed_tri U).preimage
      ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)
  have := isClosedMap_snd_of_compactSpace _ hC
  convert this using 1
  ext g
  constructor
  · rintro ⟨k, hk, t⟩
    exact ⟨(⟨k, hk⟩, g), t, rfl⟩
  · rintro ⟨⟨k, g'⟩, t, rfl⟩
    exact ⟨k.1, k.2, t⟩

theorem good_iff {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    Good G U g ↔ ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id := by
  constructor
  · rintro ⟨k, hk, s, _, rfl, t⟩
    refine ⟨k, hk, ?_⟩
    rwa [← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]
  · rintro ⟨k, hk, t⟩
    refine ⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩
    rw [← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]

theorem factor_of_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
    (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) →
    ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  intro n G hG U hU h g hg
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected
  have hclosed : IsClosed {x : G | Good G U x.1} := by
    have e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ |
        ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
      ext x
      exact good_iff hG x.2
    rw [e]
    exact (isClosed_factor hG U).preimage continuous_subtype_val
  have hopen : IsOpen {x : G | Good G U x.1} := by
    rw [isOpen_iff_eventually]
    intro x hx
    have := (continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)
    filter_upwards [this] with y hy using hy y.2
  have hone : Good G U 1 := by
    refine ⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩
    rw [Matrix.mul_one, star_mul_unitary hU]
    exact Matrix.blockTriangular_one
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩
  have hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1} := huniv ▸ Set.mem_univ _
  exact hmem

end GlobalTheory.CompanionTheory.LinRedFactor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmul
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechZero

theorem cechHZeroEquiv_cls {X : TopCat.{0}} {ι : Type} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})
    (U : ι → Opens X) (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
    (s : P.obj (op ⊤)) (σ : Cochain P U 0) (h : GroundTheory.Arith.SchemeCoh.d P U 0 σ = 0)
    (hσ : σ = (globalCocycle P U s).1) :
    GroundTheory.Arith.SchemeCoh.cechHZeroEquiv P U hP hU (GroundTheory.Arith.SchemeCoh.cls σ h) = s := by
  subst hσ
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquiv, AddEquiv.trans_apply]
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.app (op ⊤) s))).1 := by
  funext t
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, res_res, res_res]

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W φ

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (z : Sheaf.H.{0} G 0) :
    Sheaf.H.equiv₀ G' isTerminalTop (hPull f φ 0 z) =
      GroundTheory.Arith.SchemeCoh.res G'.obj (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.hom.app (op ⊤) (Sheaf.H.equiv₀ G isTerminalTop z)) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).surjective z
  change Sheaf.H.equiv₀ G' isTerminalTop (GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
    (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
      ((GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).symm
        (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop y)))) = _
  rw [AddEquiv.symm_apply_apply, GlobalTheory.SiteCoh.equiv₀_terminalEquiv,
    GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, zeroEquiv_eq_equivZero,
    GlobalTheory.SheafPull.equivZero_pull]
  rfl

theorem cechHZeroEquivH_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y)
    (hV : iSup V = ⊤) (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0) :
    (GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G' U hU : GroundTheory.Arith.SchemeCoh.cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G V hV : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  obtain ⟨s, hs⟩ := globalCocycle_surjective G.obj V G.property hV ⟨σ, (mem_cocycles σ).2 hσ⟩
  have hσs : σ = (globalCocycle G.obj V s).1 := (congrArg Subtype.val hs).symm
  apply (Sheaf.H.equiv₀ G' isTerminalTop).injective
  rw [hPull_zero, cechPullH_cls]
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [cechHZeroEquiv_cls G.obj V G.property hV s σ hσ hσs]
  refine cechHZeroEquiv_cls G'.obj U G'.property hU _ _ _ ?_
  rw [hσs]
  exact pullCoch_globalCocycle f φ.hom V U τ hτ s

end GlobalTheory.CompanionTheory.CechZero
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCechDelta

theorem app_res_nat {X : TopCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (a : Q ⟶ Q₂)
    {A B : Opens X} (h : A ≤ B) (x : Q.obj (op B)) :
    a.app (op A) (res Q h x) = res Q₂ h (a.app (op B) x) := by
  exact NatTrans.naturality_apply a (homOfLE h).op x

theorem push_pullCoch {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {P P₂ : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (a : P ⟶ P₂) (a' : Q ⟶ Q₂) (φ : P ⟶ (Opens.map f).op ⋙ Q) (φ₂ : P₂ ⟶ (Opens.map f).op ⋙ Q₂)
    (h : ∀ W x, φ₂.app W (a.app W x) = a'.app _ (φ.app W x)) (n : ℕ) (σ : Cochain P V n) :
    push U a' n (pullCoch f φ V U τ hτ n σ) = pullCoch f φ₂ V U τ hτ n (push V a n σ) := by
  funext t
  exact (app_res_nat a' _ _).trans (congrArg (res Q₂ _) (h _ _).symm)

theorem cechPullH_delta : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  intro X Y f κ ι V U τ hτ F I Q F' I' Q' g₁ g₂ g₁' g₂' hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ n σ
  obtain ⟨t, ρ, hρ, ht, hρt, hc⟩ := hC.delta_spec n σ
  have h1 : push U g₂' n (pullCoch f φ₂ V U τ hτ n t) = pullCoch f φ₃ V U τ hτ n σ.1 := by
    rw [push_pullCoch f V U τ hτ g₂ g₂' φ₂ φ₃ h₂₃ n t, ht]
  have h2 : push U g₁' (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) =
      d I' U n (pullCoch f φ₂ V U τ hτ n t) := by
    rw [push_pullCoch f V U τ hτ g₁ g₁' φ₁ φ₂ h₁₂ (n + 1) ρ, hρt, pullCoch_d]
  have h3 : d F' U (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) = 0 := by
    rw [← pullCoch_d, hρ, map_zero]
  rw [hc, cechPullH_cls]
  exact hC'.deltaRel_unique ⟨pullCoch f φ₂ V U τ hτ n t, pullCoch f φ₁ V U τ hτ (n + 1) ρ, h3, h1, h2, rfl⟩
    (hC'.delta_spec n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩)

end GlobalTheory.CompanionTheory.OmCechDelta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeWchMem

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D :=
  fun D N i h j => GlobalTheory.CompanionTheory.ConeChart.preimage_chart_mem D N i h j

end GlobalTheory.CompanionTheory.ConeWchMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w'

section LES

theorem cls_congr {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}

theorem sq_mapH {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L L' σ)
    (φ' : Cx.Hom K' L' (RingHom.id R')) (ψ' : Cx.Hom K K' σ)
    (h : ∀ n x, ψ.f n (φ.f n x) = φ'.f n (ψ'.f n x)) (n : ℕ) (z : K.H n) :
    ψ.mapH n (φ.mapH n z) = φ'.mapH n (ψ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 z
  have c1 : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have c2 : L'.d n (ψ.f n (φ.f n x)) = 0 := by rw [ψ.comm, c1, map_zero]
  have c3 : K'.d n (ψ'.f n x) = 0 := by rw [ψ'.comm, hx, map_zero]
  have c4 : L'.d n (φ'.f n (ψ'.f n x)) = 0 := by rw [φ'.comm, c3, map_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx c1, CrystallineSemistableComparison.P.mapH_cls ψ n _ c1 c2, CrystallineSemistableComparison.P.mapH_cls ψ' n x hx c3,
    CrystallineSemistableComparison.P.mapH_cls φ' n _ c3 c4]
  exact cls_congr (h n x) _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_les [∀ i, Module.Flat R (N i)]
    {K L M : ι → Cx.{w} R} {K' L' M' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) (g : ∀ i, Cx.Hom (L i) (M i) (RingHom.id R))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (f' : Cx.Hom K' L' (RingHom.id R')) (g' : Cx.Hom L' M' (RingHom.id R'))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (a : ∀ i, N i → Cx.Hom (K i) K' σ) (b : ∀ i, N i → Cx.Hom (L i) L' σ) (c : ∀ i, N i → Cx.Hom (M i) M' σ)
    (hab : ∀ i n k x, (b i n).f k ((f i).f k x) = f'.f k ((a i n).f k x))
    (hbc : ∀ i n k x, (c i n).f k ((g i).f k x) = g'.f k ((b i n).f k x))
    (hL : ∀ j, Tens R (N := N) (M := fun i => (L i).H j) (M' := L'.H j) fun i n x => (b i n).mapH j x)
    (hM : ∀ j, Tens R (N := N) (M := fun i => (M i).H j) (M' := M'.H j) fun i n x => (c i n).mapH j x)
    (hadd : ∀ i j, ∃ F : N i ⊗[R] (K i).H j →+ K'.H j, ∀ n x, F (n ⊗ₜ x) = (a i n).mapH j x) :
    ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (a i n).mapH j x := by
  intro j
  choose δ hδ h0 e1 e2 e3 using fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  obtain ⟨δ', hδ', h0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have dcomm : ∀ i n k z, (a i n).mapH (k + 1) (δ i k z) = δ' k ((c i n).mapH k z) := by
    intro i n k z
    obtain ⟨m, hm, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (M i) k).1 z
    obtain ⟨y, rfl⟩ := hg i k m
    obtain ⟨x, hx⟩ := CrystallineSemistableComparison.CechClassBoundaries.conn_ex (f i) (g i) (hfg i) y hm
    have hxc := CrystallineSemistableComparison.CechClassBoundaries.conn_cyc (f i) (hf i) y x hx
    have c3 : K'.d (k + 1) ((a i n).f (k + 1) x) = 0 := by rw [(a i n).comm, hxc, map_zero]
    have c4 : M'.d k ((c i n).f k ((g i).f k y)) = 0 := by rw [(c i n).comm, hm, map_zero]
    have c5 : M'.d k (g'.f k ((b i n).f k y)) = 0 := by rw [← hbc]; exact c4
    rw [hδ i k y x hm hxc hx, CrystallineSemistableComparison.P.mapH_cls (a i n) _ x hxc c3, CrystallineSemistableComparison.P.mapH_cls (c i n) k _ hm c4,
      cls_congr (hbc i n k y) c4 c5, hδ' k _ _ c5 c3 (by rw [← hab, hx, (b i n).comm])]
  cases j with
  | zero =>
    refine tens_five (M₁ := fun _ => PUnit.{w + 1}) (M₂ := fun _ => PUnit.{w + 1}) (L₁ := PUnit.{w' + 1}) (L₂ := PUnit.{w' + 1})
      (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
      0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
      (fun _ _ _ => 0) (fun _ _ _ => 0) _ (fun i n x => (b i n).mapH 0 x) (fun i n x => (c i n).mapH 0 x)
      (fun _ _ _ => rfl) (fun i n x => ?_) (fun i n x => ?_) (fun i n x => ?_)
      (fun i y => by simp) (fun i y => ?_) (fun i => e1 i 0)
      (fun y => by simp) (fun y => ?_) (e1' 0)
      (tens_zero (fun _ => inferInstance) inferInstance _) (tens_zero (fun _ => inferInstance) inferInstance _)
      (hL 0) (hM 0) (fun i => hadd i 0)
    · have : (0 : PUnit.{w + 1} →ₗ[R] (K i).H 0) x = 0 := rfl
      simp
    · exact sq_mapH (f i) (b i n) f' (a i n) (hab i n) 0 x
    · exact sq_mapH (g i) (c i n) g' (b i n) (hbc i n) 0 x
    · constructor
      · intro h
        have : y = 0 := h0 i (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
    · constructor
      · intro h
        have : y = 0 := h0' (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
  | succ k =>
    exact tens_five (fun i => (g i).mapH k) (fun i => δ i k) (fun i => (f i).mapH (k + 1)) (fun i => (g i).mapH (k + 1))
      (g'.mapH k).toAddMonoidHom (δ' k).toAddMonoidHom (f'.mapH (k + 1)).toAddMonoidHom (g'.mapH (k + 1)).toAddMonoidHom
      (fun i n x => (b i n).mapH k x) (fun i n x => (c i n).mapH k x) _
      (fun i n x => (b i n).mapH (k + 1) x) (fun i n x => (c i n).mapH (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) k x) (fun i n x => dcomm i n k x)
      (fun i n x => sq_mapH (f i) (b i n) f' (a i n) (hab i n) (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) (k + 1) x)
      (fun i => e2 i k) (fun i => e3 i k) (fun i => e1 i (k + 1)) (e2' k) (e3' k) (e1' (k + 1))
      (hL k) (hM k) (hL (k + 1)) (hM (k + 1)) (fun i => hadd i (k + 1))

end LES

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTiltStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_idempotent_lift_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | exact GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.existsUnique_idempotent_sharp <;> assumption)
end

