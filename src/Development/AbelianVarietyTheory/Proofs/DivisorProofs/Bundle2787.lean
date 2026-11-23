module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEval
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.BotBigLevel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV GlobalTheory.BotFinLevel
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)

variable {D : D7}

theorem topL_mul_sq {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem unitChar_congr (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (e : Formalism.L2.Theta.AE D) {k : ℕ}
    {M N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (h : M.det = N.det) : unitChar ν e M = unitChar ν e N := by
  have h1 : IsUnitDet e M = IsUnitDet e N := by
    funext x
    unfold IsUnitDet
    rw [h]
  unfold unitChar
  rw [h1]

theorem inId_mul_right {I : Ideal (𝓞 D.host.E)} {k d : ℕ} {K : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hK : IsIntM K)
    {Y : Matrix (Fin d) (Fin k) (Lev.EAf D)} {i : Fin d} (h : ∀ j, InId I (Y i j)) (j : Fin k) :
    InId I ((HMul.hMul Y K) i j) := by
  have := inId_mul (K := K.transpose) (Y := Y.transpose) (j := i) (fun a b => hK b a) h j
  rwa [← Matrix.transpose_mul] at this

theorem detIdl_inv {e : Formalism.L2.Theta.AE D} (hee : e * e = e) (S : HSp D) (g : Formalism.L2.Theta.GA D S) :
    detIdl e S g⁻¹ = (detIdl e S g)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right (Units.ext ?_)).symm
  have h1 : (Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_mul_inv, Matrix.det_one]
  rw [Units.val_mul, detIdl_val hee, detIdl_val hee, Units.val_one]
  linear_combination e * h1 + ((Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det - (Formalism.L2.Theta.mt S g).det -
    (Formalism.L2.Theta.mt S g⁻¹).det + 1) * hee

theorem stdFst_actO (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (I : Ideal (𝓞 D.host.E)) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St βS) (y : WO S T) :
    stdFst ν e I S T βS βT (actO S T g 1 y) = ((ν (detIdl e S g) : Circle) : ℂ) * stdFst ν e I S T βS βT y := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hg' : Lev.finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem hg
  have hK : (frG S βS g).1 * (frG S βS g⁻¹).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.mul_inv]
  have hK' : (frG S βS g⁻¹).1 * (frG S βS g).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.inv_mul]
  have h1 : frG T βT 1 = 1 := by
    unfold frG
    rw [map_one, mul_one, inv_mul_cancel]
  have hact : frMapO S T βS βT (actO S T g 1 y) = HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_actO, h1, Units.val_one, Matrix.one_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv]
  have hback : frMapO S T βS βT y =
      HMul.hMul (HMul.hMul (frMapO S T βS βT y) (frG S βS g⁻¹).1) (frG S βS g).1 := by
    rw [Matrix.mul_assoc, hK', Matrix.mul_one]
  unfold stdFst
  rw [hact]
  by_cases hc : IsHalf e y ∧ IsIntM (frMapO S T βS βT y) ∧ ∀ i j, S.rank ≤ i.1 → InId I (frMapO S T βS βT y i j)
  · rw [if_pos hc, if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).2 hc.1,
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul hc.2.1 (isIntM_frG hg'),
      fun i j hi => inId_mul_right (isIntM_frG hg') (fun l => hc.2.2 i l hi) j⟩, topL_mul_sq,
      unitChar_congr ν e (Matrix.det_mul_comm _ _),
      unitChar_mul ν hee hK (isUnitDet_frG he hg') (isUnitDet_frG he hg), detIdl_inv hee, map_inv, inv_inv]
  · rw [if_neg hc, if_neg, mul_zero]
    rintro ⟨h1, h2, h3⟩
    refine hc ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).1 h1, ?_, fun i j hi => ?_⟩
    · rw [hback]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul h2 (isIntM_frG hg)
    · rw [hback]; exact inId_mul_right (isIntM_frG hg) (fun l => h3 i l hi) j

theorem fix_fst_of_unram {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (s : T)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      CharUnramAt D (α s) v ∧ CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A} (hk1 : k ∈ GfC A) (hk2 : Lev.finE A k ∈ St X.rA.β) : X.ω s (k, 1) (X.f s) = X.f s := by
  have hW : IsWeilDatumO ψ (GlobalTheory.Grid.neg A) WW (β s) (β s / α s) ((X.ω s).toSgn true) := hX.weil s
  have hA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  set k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k with hk'
  have hk1' : k' ∈ GfC (GlobalTheory.Grid.neg A) := hk1
  have hk2' : Lev.finE (GlobalTheory.Grid.neg A) k' ∈ St X.rA.β := hk2
  have he := hX.idem s
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hA hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).2, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).2 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).1)⟩)
    k' hk1' 1 (one_mem _) (keeps_latHat (S := GlobalTheory.Grid.neg A) hX.rigA.2.1 hk2') (keeps_latHat hX.rigW.2.1 h1) X.vac
    hX.isVac.2.theta hX.isVac.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (β s) (β s / α s) (detIdl (idemAt w) (GlobalTheory.Grid.neg A) k')
      (detIdl (idemAt w) WW 1) : Circle) : ℂ)) = (((α s / β s) (detIdl (X.e s) (GlobalTheory.Grid.neg A) k') : Circle) : ℂ) := by
    rw [← prod_detIdl he hP, map_prod]
    rw [show ∀ f : Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, detIdl_one, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  rw [hc] at hv
  have key := GlobalTheory.SchrMove.smul_om_eq D ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW hA hX.rigW.1 (X.e s)
    hee (GlobalTheory.PlaceDatum.infPart_idemSum he) k' 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW _ _ _ _ hA hX.rigW.1 hX.rigA.2.1 hX.rigW.2.1 k' 1 hk2' h1)
    X.vac _ (X.f s) _ _ hX.isVac.2.theta (hX.fst s) (Circle.coe_ne_zero _) hv
    (stdFst_actO (α s / β s) he (X.ideal S s) (GlobalTheory.Grid.neg A) WW X.rA.β X.rW.β hk2')
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

theorem mem_St_of_isFinPt {A : HSp D} {r : Rig A} (hr : r.Is) (hs : r.IsStd) {n : ℕ} {x : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    {k : Formalism.L2.Theta.GA D A} (hx : x ∈ GlobalTheory.NormSum.intG D n) (hk : GlobalTheory.BotFormula.IsFinPt A k x) : Lev.finE A k ∈ St r.β := by
  obtain rfl : A.rank = n := hk.2.choose
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E A.rank := by
    ext y
    rw [hs.2.1 y]
    exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩
  have hβ : Formalism.L2.DIV.IsFrame r.β (Formalism.L2.Col.stdLat D.host.E A.rank) := hΛ ▸ hr.2.1
  refine (GlobalTheory.BotClassDict.mem_level_iff A hs.1 hβ k).2 ?_
  rw [GlobalTheory.BotClassDict.finStd_of_isFinPt A hs.1 hk]
  exact hx

theorem ker_mul_of_fix {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (t : T) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GfC A) (hf : X.ω t (k, 1) (X.f t) = X.f t)
    (P : PolF D WW.rank A.rank) (g : Formalism.L2.Theta.GA D WW) (y : Formalism.L2.Theta.GA D A) :
    X.ker ψ θ t P g (y * k) = X.ker ψ θ t P g y := by
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f P with hpt
  have e1 : ∀ f, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm k, 1) f = X.ω t (k, 1) f := fun f => rfl
  have move : X.ω t (k, 1) (pt (X.f t)) = pt (X.ω t (k, 1) (X.f t)) := by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.weil t) θ hX.isVac.2.inf ((GlobalTheory.Grid.ofSgn true A).symm k) hk 1
      (one_mem _) (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (GlobalTheory.ConstRatio.theta_f hX t).1
  have e2 : ∀ z, X.ker ψ θ t P g z = X.ω t (z, g) (pt (X.f t)) 0 := fun z => rfl
  have e3 : ((y * k, g) : Formalism.L2.Theta.GA D A × Formalism.L2.Theta.GA D WW) = (y, g) * (k, 1) := by
    rw [Prod.mk_mul_mk, mul_one]
  rw [e2, e2, e3, map_mul, Module.End.mul_apply, move, hf]

end GlobalTheory.BotBigLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalOfFreeHodgeBaseChangeRigid
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace GrothendieckMessing

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I}
  {π : R →+* R₀}

theorem canonical_of_free_hodge_baseChange_rigid (PF : AbelianDeRham.Free)
    (PH : AbelianDeRham.Hodge) (PB : AbelianDeRham.BaseChange) (PR : AbelianDeRham.Rigid)
    (hκ : IsNilDP κ) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) : Canonical κ π := by
  intro g A₀ _ A _ i h hA hg
  letI : Algebra R R₀ := π.toAlgebra
  obtain ⟨-, ⟨N, hN⟩, -⟩ := PH R A g hA hg
  have hF : PrimitiveSubmodule A₀ = Submodule.span R₀ ((redMor h).pull '' (PrimitiveSubmodule A)) :=
    (PB R A g hA hg R₀ A₀ i h).2
  have := (PF.prim hA hg).2.1
  refine ⟨PR R A g hA hg I κ hκ R₀ π hπ hI A₀ i h, ⟨N.dualAnnihilator, ?_, ?_⟩, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, Fil, ← Submodule.dualAnnihilator_sup_eq, hN.sup_eq_top,
      Submodule.dualAnnihilator_top]
  · refine codisjoint_iff_le_sup.2 fun x _ ↦ Submodule.mem_sup.2
      ⟨x ∘ₗ Submodule.projection _ _ hN.symm, ?_, x ∘ₗ Submodule.projection _ _ hN, ?_, ?_⟩
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero]
    · exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN).2 hc, map_zero]
    · ext c
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_add (f := _), add_comm,
        Submodule.projection_add_projection_eq_self hN]
  · intro hy
    let l : primDR A →ₗ[R] R₀ :=
      { toFun c := y ((redMor h).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₀) l hπ
    refine ⟨x ∘ₗ Submodule.projection _ _ hN.symm, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ by
        rw [LinearMap.comp_apply, (Submodule.projection_apply_eq_zero_iff hN.symm).2 hc, map_zero], fun c ↦ ?_⟩
    have z : l (Submodule.projection _ _ hN c) = 0 := (Submodule.mem_dualAnnihilator _).1 hy _
      (hF ▸ Submodule.subset_span ⟨_, Submodule.projection_apply_mem hN c, rfl⟩)
    change l c = π (x _)
    conv_lhs => rw [← Submodule.projection_add_projection_eq_self hN c, map_add (f := _), z, zero_add, ← hx]
    rfl
  · rintro ⟨x, hx, e⟩
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker y)).2 (fun c hc ↦ ?_) hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero])

end GrothendieckMessing

theorem grothendieckDeformation_of_structure (hS : AbelianDeRhamStructure)
    (hC : CrystallineDeRham) (hLift : AbelianLifting) : GrothendieckDeformation :=
  have hF : AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hS.1
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_free_hodge_baseChange_rigid hF hS.2.1 hS.2.2
      (AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hC) hκ hπ hI,
      hLift R I κ hκ R₀ π hπ hI⟩

theorem grothendieckDeformation_of_abelianLifting
    (hCrys : CrystallineSmoothLift) (hHdR : AbelianHodgeDeRham) (hLift : AbelianLifting) :
    GrothendieckDeformation :=
  grothendieckDeformation_of_structure (_root_.GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses hCrys hHdR).1 (_root_.GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses hCrys hHdR).2 hLift

theorem grothendieckDeformation₂
    (hCrys : CrystallineSmoothLift) (hHdR : AbelianHodgeDeRham) (_hDual : DualAbelianScheme)
    (_hPoinc : PoincareDeRhamDuality) (hLift : AbelianLifting) : GrothendieckDeformation :=
  grothendieckDeformation_of_abelianLifting hCrys hHdR hLift

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLattic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescSpan

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (g : S →+* T) (h : R →+* S) :
    spMap (g.comp h) = spMap g ≫ spMap h := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (Desc.cst p) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_naturality]
  ext r
  simp [Desc.cst, Cartier.fnOf]

theorem cst_comp_spMap {X : Scheme.{0}} [IsIntegral X] {R S : Type} [CommRing R] [CommRing S] (p : X ⟶ Sp S)
    (g : R →+* S) : Desc.cst (p ≫ spMap g) = (Desc.cst p).comp g := by
  have h : spMap (Desc.cst (p ≫ spMap g)) = spMap ((Desc.cst p).comp g) := by
    rw [spMap_comp', ← gp_comp, ← gp_comp, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (q : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst q r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) (r : σ.R) :
    σ.θ x (σ.c₀ r) = Desc.cst (σ.C x).G.hom (σ.ρ x r) := by
  obtain ⟨l, h1, h2⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, Category.assoc,
      (σ.cart x).w, ← Category.assoc, ← Category.assoc, h1, Category.assoc]
  exact congrArg (fun q : σ.R →+* _ => q r) (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

theorem mem_W_mul (σ : Setup) (x : Sp σ.R) {u : σ.A.left.functionField} (hu : u ∈ σ.W x) (r : σ.R) :
    σ.c₀ r * u ∈ σ.W x := fun z hz => by
  rw [map_mul, theta_c₀]
  exact (regAt_cst _ _ _).mul (hu z hz)

section Sec

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {k : ℕ}

theorem sec_zero : (0 : X.functionField) ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [zero_mul]; exact regAt_zero x)

theorem sec_add {u v : X.functionField} (hu : u ∈ Sec D k) (hv : v ∈ Sec D k) : u + v ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [add_mul]; exact (hg.regularAt_iff.1 (hu x)).add (hg.regularAt_iff.1 (hv x)))

theorem sec_mul {u c : X.functionField} (hu : u ∈ Sec D k) (hc : ∀ x, RegAt x c) : c * u ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [_root_.mul_assoc]; exact (hc x).mul (hg.regularAt_iff.1 (hu x)))

end Sec

theorem finite_vert (σ : Setup) :
    {p : Sp σ.R | p.asIdeal.height = 1 ∧ σ.f ∈ p.asIdeal}.Finite := by
  have hfin := (Ideal.span {σ.f}).finite_minimalPrimes_of_isNoetherianRing
  refine (hfin.preimage fun a _ b _ h => PrimeSpectrum.ext h).subset fun p hp => ?_
  obtain ⟨h1, hf⟩ := hp
  have : p.asIdeal.FiniteHeight := (Ideal.finiteHeight_iff _).2 (Or.inr (by rw [h1]; exact ENat.one_ne_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hf) ?_
  rw [h1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero σ.hf)

end GlobalTheory.DescSpan


open GlobalTheory.DescSpan in
theorem GlobalTheory.Desc.sec_eq_spanBy_N : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  intro σ k
  have hc₀ : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := cst_comp_spMap _ _
  ext u
  constructor
  · intro hu
    choose m hm using fun p : Sp σ.R => _root_.GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart σ p u
    let M := ∑ p ∈ (finite_vert σ).toFinset, m p
    let v := σ.c₀ (σ.f ^ M) * u
    have hv : v ∈ σ.N k := by
      refine ⟨sec_mul hu fun x => by rw [hc₀]; exact regAt_cst _ _ _, (_root_.GlobalTheory.Desc.Setup.forall_mem_W_iff σ v).2 fun p h1 hf => ?_⟩
      have hle : m p ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        ((finite_vert σ).mem_toFinset.2 ⟨h1, hf⟩)
      have e : v = σ.c₀ (σ.f ^ (M - m p)) * (σ.c₀ σ.f ^ m p * u) := by
        simp only [v, map_pow]
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact mem_W_mul σ p (hm p) _
    refine ⟨1, fun _ => IsLocalization.Away.invSelf σ.f ^ M, fun _ => v, fun _ => hv, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [v, hc₀, RingHom.comp_apply, map_pow]
    rw [← _root_.mul_assoc, ← mul_pow, ← map_mul, mul_comm (IsLocalization.Away.invSelf σ.f),
      IsLocalization.Away.mul_invSelf, map_one, one_pow, _root_.one_mul]
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Finset.sum_induction _ (· ∈ Sec σ.D k) (fun _ _ => sec_add) sec_zero
      fun i _ => sec_mul (ht i).1 fun x => regAt_cst _ _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.ClsOrb

theorem clsSum_eq_mass_mul_twOrb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf γ hγ
  obtain ⟨hKo, hKc, hlev⟩ := GlobalTheory.T.productOfLocalLevelsUnitary_isOpen_isCompact_isLevel E hU n hn S hS K' hK'
  have hH := _root_.GlobalTheory.BCT.GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hcomm := GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm E n γ hγ
  have hcpt := GlobalTheory.T.level_stabiliser_le_centraliser_compact_part E hU n hn S hS K' hK' γ hγ
  have hsupp := GlobalTheory.T.regularRationalPoint_testSupport_doubleCosets_finite E hU n hn S hS K' hK' f hf γ hγ
  have horb := GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel (finU (E := E) (n := n)) (MonoidHom.id _) (globLev S (KL n)) hKo hKc
    (fun k hk => hk) (globLev S K') hlev (finPt γ) (globFn S f) hH hcpt hsupp
  set T := twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) with hT
  have hCT : cptPart T ≤ T := (Subgroup.closure_le T).2 fun t ht => ht.1
  have hU' : ∀ x : finU (E := E) (n := n), T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
      (T ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0 := fun x =>
    ⟨le_trans (inf_le_inf_left _ (Subgroup.map_mono hlev.2.1)) (hcpt x).1, (hcpt x).2⟩
  have hinv : ∀ t ∈ T, ∀ k ∈ globLev S K', ∀ x : finU (E := E) (n := n),
      globFn S f ((t * x * k)⁻¹ * finPt γ * (t * x * k)) = globFn S f (x⁻¹ * finPt γ * x) := by
    intro t ht k hk x
    have ht' : t * finPt γ = finPt γ * t := ht
    have e1 : t⁻¹ * finPt γ * t = finPt γ := by
      rw [mul_assoc, ← ht', ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : (t * x * k)⁻¹ * finPt γ * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * finPt γ * t) * x) * k := by group
    rw [e2, e1, mul_assoc, (hH.2 k⁻¹ (inv_mem hk) _).1, (hH.2 k hk _).2]
  have hreg := GlobalTheory.T.finsum_doubleCoset_regroup_commutative (finU (E := E) (n := n)) T (ratFinU E n) (cptPart T) (globLev S K')
    (fun x => globFn S f (x⁻¹ * finPt γ * x)) hcomm hCT hU' hinv
  simp only [MonoidHom.id_apply] at horb
  rw [clsSum, horb.1, horb.2, hreg, mass]
  ring

end GlobalTheory.BCT.ClsOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (τ : S.Test p y₀) (ε : D.toPre.X ≃+ τ.X), (∀ α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-τ.q (ε α))) ∧ ∀ a α, yy a = QuotientAddGroup.mk α ↔ τ.yy a = QuotientAddGroup.mk (ε α) := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hCpl G _ _ gm hpb D A U hLB hPsi
  obtain ⟨yy, hyy⟩ := _root_.GlobalTheory.Poinc.LabConst.main o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
  refine ⟨yy, ?_⟩
  intro p _ y ev hCen hev y₀ hAt
  obtain ⟨u, ε₀, hbc⟩ := _root_.GlobalTheory.Poinc.TestAtPt.exists_uTest_isBC o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hBase hCpl G gm hpb D A U hLB hPsi
    p y ev hCen hev y₀ hAt
  have hint : ∀ a : o', ‖y₀ (algebraMap o' S.R a)‖ ≤ 1 := by
    intro a
    rw [hAt]
    exact hCen.norm_val_le_one ((M.O x).algebraMap_mem a)
  have hL := GlobalTheory.firstFiveLaws.1
  have hL2 := GlobalTheory.firstFiveLaws.2.1
  have hT := GlobalTheory.ZH.uTors_closed
  obtain ⟨l⟩ := _root_.GlobalTheory.ZH.labels_exist hL hL2 hT o' Ω S ρ p y₀ u hint
  obtain ⟨τ, e, hq, hy⟩ := exists_test_match o' Ω S ρ p y₀ u l
    (_root_.GlobalTheory.ZH.TestVal.main hL hL2 hT o' Ω S ρ p y₀ u l hint) (_root_.GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (_root_.GlobalTheory.ZH.WeightBound.main hL hL2 hT o' Ω S ρ p y₀ u l hint) (_root_.GlobalTheory.TestFibre.exists_norm_FF_eq hL hL2 hT o' Ω S ρ p y₀ u l hint)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hT o' Ω S ρ p y₀ u l hint)
  refine ⟨τ, ε₀.trans e.symm, ?_, ?_⟩
  · intro α s hs
    rw [_root_.GlobalTheory.Poinc.TestAtPt.norm_psi_coord o' Ω S ρ M U₀ EE FinalForm R G gm D A U p y₀ ev u ε₀ hbc l α s hs, AddEquiv.trans_apply, hq,
      AddEquiv.apply_symm_apply]
  · intro a α
    rw [hyy p y ev hCen hev y₀ hAt u ε₀ hbc l a α, AddEquiv.trans_apply, hy, AddEquiv.apply_symm_apply]

end GlobalTheory.Poinc.TestAtPt
end
end

