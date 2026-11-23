module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat.EmbedsBC
theorem embeds_bc : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  intro Rg _ B _ M k mB bB hAb hM hVA hBC
  have : UniversallyClosed B.hom := by
    have := hAb.proper
    infer_instance
  let x : Sp Rg ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  have hx : IsIso x := inferInstanceAs (IsIso (Sp Rg).topIso.inv)
  choose b' hb' using fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_isPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i)
  refine ⟨x, b', hx, hb', ?_⟩
  have hsp := (hBC Rg x b' hb').2
  exact GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) x b' hsp
end GlobalTheory.HomFixMat.EmbedsBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectively
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HomFixGerm

open GlobalTheory.AmpleSpan

theorem eq_of_germs {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N)
    (hs : EmbedsBy π s) (f₁ f₂ : X ⟶ Y) (hπ : f₁ ≫ π = f₂ ≫ π)
    (h : ∀ x : X, ∃ σ : κ → X.presheaf.stalk x,
      (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧
      (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) :
    f₁ = f₂ := by
  have mem : ∀ x l, f₁ x ∈ nonzeroLocus (s l) ↔ f₂ x ∈ nonzeroLocus (s l) := by
    intro x l
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    rw [mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁, mem_nonzeroLocus_iff_gs (s l) f₂ x hp₂, e₁ l, e₂ l,
      Units.isUnit_units_mul, Units.isUnit_units_mul]
  have rat : ∀ (l : κ) (r : κ → Γ(Y, nonzeroLocus (s l))), (∀ j, IsRatio (s j) (s l) (r j)) →
      ∀ x j, f₁ x ∈ nonzeroLocus (s l) → gs f₁ x _ (r j) = gs f₂ x _ (r j) := by
    intro l r hr x j hx
    have hx₂ := (mem x l).1 hx
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    have a₁ := (hr j).gs f₁ x hx hp₁
    have a₂ := (hr j).gs f₂ x hx₂ hp₂
    rw [e₁ j, e₁ l] at a₁
    rw [e₂ j, e₂ l] at a₂
    have hσ : IsUnit (σ l) := by
      have := (mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁).1 hx
      rwa [e₁ l, Units.isUnit_units_mul] at this
    have b₁ : σ j = gs f₁ x _ (r j) * σ l := by
      apply u₁.isUnit.mul_left_cancel
      rw [a₁]; ring
    have b₂ : σ j = gs f₂ x _ (r j) * σ l := by
      apply u₂.isUnit.mul_left_cancel
      rw [a₂]; ring
    exact hσ.mul_right_cancel (b₁.symm.trans b₂)
  have loc : ∀ l, (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₁ = (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₂ := by
    intro l
    obtain ⟨haff, r, hr, hsurj⟩ := hs.2 l
    have hV : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ f₂ ⁻¹ᵁ nonzeroLocus (s l) := fun x hx => (mem x l).1 hx
    have happ : f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      have hcomp : (f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) =
          (f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) := by
        refine MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp, gs_appLE π ⊤ _ le_top f₁ x hx, gs_appLE π ⊤ _ le_top f₂ x (hV hx), hπ]
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp]
          exact rat l r hr x j hx
      ext a
      obtain ⟨P, rfl⟩ := hsurj a
      exact congrArg (fun φ : MvPolynomial κ Γ(Z, ⊤) →+* _ => φ P) hcomp
    haveI : IsAffine (nonzeroLocus (s l)) := haff
    have hres : f₁.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      refine ext_of_isAffine ?_
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]
    rw [← Scheme.Hom.resLE_comp_ι f₁ (le_rfl : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ _),
      ← Scheme.Hom.resLE_comp_ι f₂ hV, hres]
  have hcov : TopologicalSpace.IsOpenCover (fun l => f₁ ⁻¹ᵁ nonzeroLocus (s l)) := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show f₁ x ∈ ⨆ l, nonzeroLocus (s l) by rw [hs.1]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hl⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _ hcov) f₁ f₂ fun l => loc l

end GlobalTheory.HomFixGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatNhds

open GlobalTheory.SplitScalar

variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_actO (S T : HSp D) (x : WO S T) :
    Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x := by
  have h1 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt T p.2 := (continuous_mt T).comp continuous_snd
  have h2 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt S p.1⁻¹ := (continuous_mt_inv S).comp continuous_fst
  exact (h1.matrix_mul continuous_const).matrix_mul h2

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  have h : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun _ => rfl
  rw [actO, inv_one, h, h, Matrix.one_mul, Matrix.mul_one]

theorem actO_smul {S T : HSp D} (g : GA D S) (h : GA D T) (a : AE D) (x : WO S T) :
    actO S T g h (a • x) = a • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem fin_iff {S T : HSp D} {u : WO S T} : u.map (infPart D) = 0 ↔ realIdem D • u = 0 := by
  constructor
  · exact fun h => Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun h i) j)
  · intro h
    funext i j
    have h1 := congrArg (infPart D) (congrFun (congrFun h i) j)
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, infPart_realIdem, one_mul] at h1
    exact h1.trans (infPart D).map_zero

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  rw [fin_iff] at hu ⊢
  rw [← actO_smul, hu, actO, Matrix.mul_zero, Matrix.zero_mul]

theorem continuous_sub_const' {X G : Type} [TopologicalSpace X] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : X → G} (hf : Continuous f) (x : G) : Continuous fun p => f p - x :=
  hf.sub continuous_const

theorem sub_nsmul_zero {G : Type} [AddCommGroup G] (x : G) (N : ℕ) : x - x - N • (0 : G) = 0 := by
  rw [sub_self, smul_zero, sub_self]

theorem eventually_move (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (x : WO S T) (hx : x.map (infPart D) = 0) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  have hO := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT N hN
  have hc : Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x - x :=
    continuous_sub_const' (continuous_actO S T x) x
  have h1 := (hO.preimage hc).mem_nhds (x := 1) ⟨0, AddSubgroup.zero_mem _, by
    show (actO S T 1 1 x - x - N • (0 : WO S T)).map (finPart D) = 0
    rw [actO_one, sub_nsmul_zero]
    exact Matrix.ext fun _ _ => (finPart D).map_zero⟩
  filter_upwards [h1] with p hp
  obtain ⟨l, hl, e⟩ := hp
  refine ⟨l, hl, ?_⟩
  have hi : (actO S T p.1 p.2 x - x - N • l).map (infPart D) = 0 := by
    have a1 := fin_iff.1 (actO_fin p.1 p.2 hx)
    have a2 := fin_iff.1 hx
    have a3 := fin_iff.1 (latO_fin (AddSubgroup.nsmul_mem _ hl N))
    rw [fin_iff, smul_sub, smul_sub, a1, a2, a3, sub_zero, sub_zero]
  have hz : actO S T p.1 p.2 x - x - N • l = 0 :=
    Matrix.ext fun i j => adele_ext ((congrFun (congrFun hi i) j).trans (infPart D).map_zero.symm)
      ((congrFun (congrFun e i) j).trans (finPart D).map_zero.symm)
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

theorem eventually_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  rintro D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  refine ⟨?_, eventually_move S T ΛS ΛT hS hT⟩
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) 1 one_pos
  filter_upwards [h] with p hp
  intro w hw
  refine hgen (AddSubgroup.comap (AddMonoidHom.mk' (actO S T p.1 p.2) (actO_add p.1 p.2))
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply, actO_smul, e]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _
    (AddSubgroup.add_mem _ (hGl u hu) (AddSubgroup.nsmul_mem _ hl 1))
  exact AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩

end GlobalTheory.LatNhds

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOne
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smoothMatInf_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 →
    ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧
      tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  intro E _ _ n W hW h1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) := by
    open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))
  have hS0 : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
    have e : {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} =
        Set.range (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) :=
      Set.ext fun x => ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
    rw [e]; exact hemb.isOpen_range
  have hGL : ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
    rw [hemb.isInducing.continuousOn_iff]
    exact continuousOn_id.congr fun x hx => val_toGLInf hx
  set S : Set (Fin n → Fin n → Cinf E) := {x | IsUnit (Matrix.of x)} with hSdef
  have hS : IsOpen S := hS0
  have hF : ContinuousOn (fun x : Fin n → Fin n → Cinf E => onMatInf W (Matrix.of x)) S := by
    refine (hW.comp_continuousOn hGL).congr fun x hx => ?_
    exact onMatInf_of_isUnit W hx
  set c : ℂ := starRingEnd ℂ (W 1) with hc
  set U : Set (Fin n → Fin n → Cinf E) := S ∩ (fun x => (c * onMatInf W (Matrix.of x)).re) ⁻¹' Set.Ioi 0 with hUdef
  have hU : IsOpen U :=
    (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hF)).isOpen_inter_preimage hS isOpen_Ioi
  set x0 : Fin n → Fin n → Cinf E := fun i j => (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j with hx0def
  have hx0 : Matrix.of x0 = 1 := by ext i j; rfl
  have hval : onMatInf W (Matrix.of x0) = W 1 := by
    rw [hx0]; simpa using onMatInf_val W 1
  have hpos : 0 < (c * W 1).re := by
    rw [hc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h1
  have hx0U : x0 ∈ U := by
    refine ⟨?_, ?_⟩
    · show IsUnit (Matrix.of x0); rw [hx0]; exact isUnit_one
    · show 0 < (c * onMatInf W (Matrix.of x0)).re; rw [hval]; exact hpos
  obtain ⟨ρ, h1ρ, h2ρ, h3ρ, h4ρ, h5ρ⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx0U)
  have hts : tsupport (fun x => (ρ x : ℂ)) ⊆ U :=
    (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) ρ).trans h1ρ
  have hcs : HasCompactSupport (fun x => (ρ x : ℂ)) := h2ρ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨fun x => (ρ x : ℂ), Complex.ofRealCLM.contDiff.comp h3ρ, hcs, hts.trans Set.inter_subset_left, ?_⟩
  set f : (Fin n → Fin n → Cinf E) → ℂ := fun a => (ρ a : ℂ) * onMatInf W (Matrix.of a) with hfdef
  have e : smoothMatInf (fun x => (ρ x : ℂ)) W 1 = ∫ a, f a := by
    simp [smoothMatInf, f]
  have hsub : tsupport f ⊆ S := tsupport_mul_subset_left.trans (hts.trans Set.inter_subset_left)
  have hfc : Continuous f :=
    ((Complex.continuous_ofReal.comp h3ρ.continuous).continuousOn.mul hF).continuous_of_tsupport_subset hS hsub
  have hfs : HasCompactSupport f := hcs.mul_right
  have hint : Integrable f volume := hfc.integrable_of_hasCompactSupport hfs
  have hnn : ∀ a, 0 ≤ (c * f a).re := by
    intro a
    have hr : 0 ≤ ρ a := (h4ρ ⟨a, rfl⟩).1
    have eq : (c * f a).re = ρ a * (c * onMatInf W (Matrix.of a)).re := by
      simp only [f]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [eq]
    by_cases ha : ρ a = 0
    · simp [ha]
    · have : a ∈ U := h1ρ (subset_tsupport _ ha)
      exact mul_nonneg hr (le_of_lt this.2)
  have hne : (c * f x0).re ≠ 0 := by
    simp only [f]
    rw [h5ρ, hval]
    simpa using hpos.ne'
  have hcont : Continuous fun a => (c * f a).re := Complex.continuous_re.comp (continuous_const.mul hfc)
  have hsupp : HasCompactSupport fun a => (c * f a).re :=
    hfs.comp_left (g := fun z : ℂ => (c * z).re) (by simp)
  have key : 0 < ∫ a, (c * f a).re ∂volume :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnn (x := x0) hne
  have hre : ∫ a, (c * f a).re = (∫ a, c * f a).re := integral_re (hint.const_mul c)
  rw [e]
  intro h0
  rw [hre, integral_const_mul, h0, mul_zero, Complex.zero_re] at key
  exact lt_irrefl _ key

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.AffineTrivLocus

theorem exists_closed_triv : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro R _ A _ L₀ N hA hL₀ hamp hN hrig
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp R) A L₀ hA hL₀ hamp R (𝟙 _)
      A.left (𝟙 _) A.hom (IsPullback.id_horiz A.hom)).1
  let T0 : Over (Sp R) := Over.mk (𝟙 _)
  have h₀ : IsPullback (pullback.snd T0.hom A.hom) (fst T0 A).left A.hom T0.hom :=
    (IsPullback.of_hasPullback T0.hom A.hom).flip
  obtain ⟨F, hFd⟩ : ∃ F : LB (T0 ⊗ A).left, F = N.pull (pullback.snd T0.hom A.hom) := ⟨_, rfl⟩
  have hF : F.IsLB := hFd ▸ LB.isLB_pull hN _
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv GlobalTheory.SemiRigid.globalFns R T0 A hA hproj F hF
  refine ⟨H.left, j.left, hj, ?_⟩
  intro T t A' _ φ' hφ
  let T' : Over (Sp R) := Over.mk t
  let x : T' ⟶ T0 := Over.homMk t (Category.comp_id t)
  have hR : (∃ y : T' ⟶ H, y ≫ j = x) ↔ ∃ z : T ⟶ H.left, z ≫ j.left = t := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (fun g => g.left) hy⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · change z ≫ H.hom = t
        rw [← Over.w j]
        change z ≫ j.left ≫ 𝟙 _ = t
        rw [Category.comp_id, hz]
      · exact Over.OverMorphism.ext hz
  rw [← hR, ← hH T' x]
  have h₄ : IsPullback (x ▷ A).left (fst T' A).left (fst T0 A).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  have hw : φ' ≫ A.hom = (A'.hom ≫ t) ≫ T0.hom := by
    rw [hφ.1.w]; exact (Category.comp_id _).symm
  let φ'' : A'.left ⟶ (T0 ⊗ A).left := h₀.lift φ' (A'.hom ≫ t) hw
  have hsq : IsPullback φ'' A'.hom (fst T0 A).left t := by
    refine IsPullback.of_right (h₁₂ := pullback.snd T0.hom A.hom) (h₂₂ := T0.hom) ?_ (h₀.lift_snd _ _ _) h₀
    rw [h₀.lift_fst]
    exact (Category.comp_id t).symm ▸ hφ.1
  have e₁ : (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧
      GlobalTheory.AbLaw.Triv ((F.pull (x ▷ A).left).pull ((fst T' A).left ⁻¹ᵁ U).ι)) ↔
      GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T'.left x.left := by
    rw [GlobalTheory.TrivSubscheme.locTrivOver_iff h₄]
    exact forall_congr' fun p => exists_congr fun U => and_congr_right fun _ =>
      GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _
  rw [e₁]
  show _ ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T t
  rw [GlobalTheory.TrivSubscheme.locTrivOver_iff hsq]
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  constructor
  · intro ht τ
    refine ⟨⊤, trivial, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]
    exact GlobalTheory.AbLaw.CubeOpen.triv_comp _ rfl ht
  · intro h
    refine _root_.GlobalTheory.RigTriv.exists_gen_of_locally_trivial T A' (N.pull φ') hA' (LB.isLB_pull hN φ') (GlobalTheory.PolBaseChange.rigidified_pull hφ hrig)
      fun τ => ?_
    obtain ⟨V, hV, ht⟩ := h τ
    refine ⟨V, hV, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst] at ht
    exact (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).2 ht

end GlobalTheory.AffineTrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnit
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory

theorem tsum_pow_eventually_ne_zero : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  intro ι a i0 k0 h0 h1 hlt hs N
  classical
  have hlim : Filter.Tendsto (fun k : ℕ => ∑' i, a i ^ k) Filter.atTop
      (nhds (∑' i, (if i = i0 then (1:ℂ) else 0))) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖ ^ k0) hs
    · intro i
      by_cases hi : i = i0
      · subst hi; simp [h0]
      · simp only [hi, if_false]
        exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hlt i hi)
    · filter_upwards [Filter.eventually_ge_atTop k0] with k hk i
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (h1 i) hk
  rw [tsum_ite_eq] at hlim
  have hev := hlim.eventually_ne one_ne_zero
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetractStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → ∀ (V : Y.Opens) (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M), IsOn W₁ L → IsOn W₂ M → p ⁻¹ᵁ V ≤ W₁ → p ⁻¹ᵁ V ≤ W₂ → IsoOn (p ⁻¹ᵁ V) L M w → RigOn e L r → RigOn e M r' → ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  first | exact @GlobalTheory.PicGlue.exists_norm | exact GlobalTheory.PicGlue.exists_norm | (intros; apply GlobalTheory.PicGlue.exists_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpan
section
namespace GlobalTheory.Proof.CoeffSpan

theorem finiteDimensional_coeffSpan (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine ⟨{ toFun := fun A => ℓ (A w), map_add' := fun A B => by simp, map_smul' := fun c A => by simp }, ?_⟩
    rfl
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.Proof.CoeffSpan
end

