module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadRegularDivLocalEquationsProperFibre
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.Spread

theorem isOpen_good {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (D : EffCartierData M.Z) (G : Ω) :
    IsOpen {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨j, hj⟩ : ∃ j, x ∈ D.U j := by
    have : x ∈ (⨆ i, D.U i) := D.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨(D.U j : Set M.Z) ∩ {w | G / valF M.pt (D.U j) (D.f j) ∈ M.O w}, ?_,
    (D.U j).isOpen.inter (M.isOpen_setOf_mem_O _), hj, hx _ ⟨j, hj, rfl⟩⟩
  rintro w ⟨hwj, hwG⟩ f' ⟨k, hwk, rfl⟩
  obtain ⟨u, hu⟩ := D.assoc j k
  have hne : ((D.U j ⊓ D.U k : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwj, hwk⟩
  have e1 : valF M.pt (D.U k) (D.f k) =
      valF M.pt (D.U j) (D.f j) * valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) := by
    rw [← M.valF_resG inf_le_right hne (D.f k), ← hu, ← M.res_apply _ hne, map_mul, M.res_apply, M.res_apply,
      M.valF_resG inf_le_left hne]
  have e2 : valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)) *
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) = 1 := by
    rw [← M.res_apply _ hne, ← M.res_apply _ hne, ← map_mul, Units.mul_inv, map_one]
  have e3 : (valF M.pt (D.U j ⊓ D.U k) (u : Γ(M.Z, D.U j ⊓ D.U k)))⁻¹ =
      valF M.pt (D.U j ⊓ D.U k) ((u⁻¹ : (Γ(M.Z, D.U j ⊓ D.U k))ˣ) : Γ(M.Z, D.U j ⊓ D.U k)) :=
    inv_eq_of_mul_eq_one_right e2
  rw [e1, div_mul_eq_div_div, div_eq_mul_inv _ (valF M.pt (D.U j ⊓ D.U k) _), e3]
  exact mul_mem hwG (RatModel.valF_mem_O (show w ∈ D.U j ⊓ D.U k from ⟨hwj, hwk⟩) _)

end GlobalTheory.Poinc.Spread

theorem GlobalTheory.Poinc.spread_regular_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (z : M₁.Z) (G : Ω), G ∈ M₁.O z → (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x') → ∃ (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), z ∈ V.1 ∧ valF M₁.pt V.1 g = G ∧ ∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → G / f' ∈ M.O x' := by
  intro o Ω _ _ _ M₁ M π _ hP D z G hG hfib
  set Good : Set M.Z := {x' : M.Z | ∀ f', EqAt M D x' f' → G / f' ∈ M.O x'} with hGood
  have hcl : IsClosed (π.base '' Goodᶜ) :=
    π.isClosedMap _ (Spread.isOpen_good M D G).isClosed_compl
  have hz : z ∉ π.base '' Goodᶜ := by
    rintro ⟨x', hx', rfl⟩
    exact hx' (hfib x' rfl)
  have hW : z ∈ ({w | G ∈ M₁.O w} ∩ (π.base '' Goodᶜ)ᶜ : Set M₁.Z) := ⟨hG, hz⟩
  obtain ⟨V, hV, hzV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, (M₁.isOpen_setOf_mem_O G).inter hcl.isOpen_compl⟩) hW
  have hmem : G ∈ M₁.ringOn (V : Set M₁.Z) := RatModel.mem_ringOn.2 fun w hw => (hVW hw).1
  obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists ⟨z, hzV⟩).1 hmem
  refine ⟨⟨V, hV⟩, g, hzV, hg, fun x' hx' => ?_⟩
  by_contra h
  exact (hVW hx').2 ⟨x', h, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionBaseChangeAlgebraMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecBC

theorem sqDec_baseChange : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  intro k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc
  have hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀,
      IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left := by
    intro i
    haveI := hβ i
    obtain ⟨g, hg, e⟩ := GlobalTheory.HomDescent.exists_specialise (β i) ρ
    refine ⟨g, hg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]
    · have w₁ := Over.w g
      have w₂ := Over.w (β i)
      simp only [Over.pullback_obj_hom] at w₁ w₂
      rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]
  choose g hgm hgc using hg'
  refine ⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩
  set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR
  set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS
  have efS : fS = bc ≫ fR := (GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm
  have pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f) :=
    fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
  have i1 := lbIso_lbPow_pull hL fS N
  have i2 := GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS
  have i3 := pullIso (lbIso_lbPow_pull hL fR N).symm bc
  have i4 := pullIso H bc
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left) := by
    intro o
    cases o with
    | none => simp
    | some i => exact hgc i
  have i5 := (GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm
  have i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)))
      (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by
    obtain ⟨w, hw⟩ := (GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm
    exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩
  have j1 := i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _)
    (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2
  have j2 := j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _)
    (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3
  have j3 := j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4
  have j4 := j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _)
    (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5
  exact j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _)
    (LB.isLB_linComb (pull_isLB hM _) _ _) i6

end GlobalTheory.SqDecBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFinitelyGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [Field k] (A₀ : Over (Sp k))

theorem lbIso_lbPow_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {L : LB A₀.left} (hL : L.IsLB) (N : ℕ) :
    LBIso (lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) N)
      ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) N).pull (bcMap A₀.hom ρ)) := by
  have h₁ : LBIso (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hL _ (bcMap_fst A₀.hom ρ).symm
  have hR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow (pull_isLB hR _) N)
    (pull_isLB (isLB_lbPow hR N) _) (lbIso_lbPow h₁ N) (lbIso_lbPow_pull hR _ N)

theorem lbIso_linComb_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {M : LB A₀.left} (hM : M.IsLB) {K : Type} [Fintype K]
    (φS : K → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))))
    (φR : K → (pullback A₀.hom (spMap (algebraMap k R)) ⟶ pullback A₀.hom (spMap (algebraMap k R))))
    (ε : K → ℤ) (hφ : ∀ o, φS o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ φR o) :
    LBIso (LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) φS ε)
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) φR ε).pull (bcMap A₀.hom ρ)) := by
  have hR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have h₁ : LBIso (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hM _ (bcMap_fst A₀.hom ρ).symm
  exact LBIso.trans (LB.isLB_linComb (pull_isLB hM _) _ _) (LB.isLB_linComb (pull_isLB hR _) _ _)
    (pull_isLB (LB.isLB_linComb hR _ _) _) (PelPrim.lbIso_linComb h₁ φS ε)
    (SymExtend.lbIso_linComb_pull hR (bcMap A₀.hom ρ) φS φR ε (bcMap A₀.hom ρ) hφ)

theorem comm_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    (f : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)
    (g : (Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀)
    (h : bcMap A₀.hom ρ ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ g.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, Category.assoc, h]
  · have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
    have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
    rw [Category.assoc, bcMap_snd, ← Category.assoc, hf, Category.assoc, hg, bcMap_snd]

def fam {S : Type} [CommRing S] [Algebra k S] {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)) :
    Option (Fin r) → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))) :=
  fun o => o.elim (𝟙 _) fun i => (β i).left

theorem fam_comm {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀))
    (gam : Fin r → ((Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀))
    (h : ∀ i, bcMap A₀.hom ρ ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _) (o : Option (Fin r)) :
    fam A₀ β o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ fam A₀ gam o := by
  cases o with
  | none => simp [fam]
  | some i => exact comm_bc A₀ ρ (β i) (gam i) (h i)

end GlobalTheory.SqDecSpread


open GlobalTheory.Spread GlobalTheory.HomDescent GlobalTheory.SqDecSpread in
theorem GlobalTheory.SqDecSpread.sqDec_fg : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀],
    IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω))))
      (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) →
    ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀)
      (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  intro k Ω _ _ _ A₀ _ hA L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have := hA.proper
  have := hA.smooth
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  choose Ri g hRi hg hgeq using fun i => haveI := hβ i; exists_fg_isMonHom (A := A₀) (A' := A₀) (β i)
  let R₁ : Subalgebra k Ω := ⨆ i, Ri i
  have hR₁ : R₁.FG := fg_iSup hRi
  choose gam hgam hgameq using fun i => haveI := hg i; exists_specialise (g i) (Subalgebra.inclusion (le_iSup Ri i))
  have key₁ : ∀ i, bcMap A₀.hom R₁.val ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _ := by
    intro i
    rw [hgameq i, ← Category.assoc, bcMap_comp_of_eq A₀.hom (Subalgebra.inclusion (le_iSup Ri i)) R₁.val (Ri i).val
      (fun _ => rfl), hgeq i]
  have hL₁ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hM₁ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hLΩ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have hMΩ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have H₁ : LBIso ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) N).pull (baseChangeMap A₀.hom R₁.val))
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) (fam A₀ gam) ε).pull
        (baseChangeMap A₀.hom R₁.val)) :=
    LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (isLB_lbPow hLΩ N) (pull_isLB (LB.isLB_linComb hM₁ _ _) _)
      (lbIso_lbPow_bc A₀ R₁.val hL N).symm
      (LBIso.trans (isLB_lbPow hLΩ N) (LB.isLB_linComb hMΩ _ _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) H
        (lbIso_linComb_bc A₀ R₁.val hM (fam A₀ β) (fam A₀ gam) ε (fam_comm A₀ R₁.val β gam key₁)))
  obtain ⟨R, hR, hRfg, H₂⟩ := exists_fg_lbIso A₀.hom hR₁ _ _ (isLB_lbPow hL₁ N) (LB.isLB_linComb hM₁ _ _) H₁
  choose δ hδ hδeq using fun i => haveI := hgam i; exists_specialise (gam i) (Subalgebra.inclusion hR)
  have hLR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have hMR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  refine ⟨R, hRfg, N, a₀, r, a, δ, hN, ha₀, hδ, ?_⟩
  exact LBIso.trans (isLB_lbPow hLR N) (pull_isLB (isLB_lbPow hL₁ N) _) (LB.isLB_linComb hMR _ _)
    (lbIso_lbPow_bc A₀ (Subalgebra.inclusion hR) hL N)
    (LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) (LB.isLB_linComb hMR _ _) H₂
      (lbIso_linComb_bc A₀ (Subalgebra.inclusion hR) hM (fam A₀ δ) (fam A₀ gam) ε
        (fam_comm A₀ (Subalgebra.inclusion hR) δ gam fun i => (hδeq i).symm)).symm)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SmoothStalkNormal

theorem flat_fromSpecStalk' (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

theorem injective_of_flat_of_isDomain {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Nontrivial B] (f : A →+* B) (hf : f.Flat) : Function.Injective f := by
  algebraize [f]
  refine (injective_iff_map_eq_zero f).2 fun r hr => ?_
  by_contra h0
  have hreg : IsSMulRegular B r :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero h0)
  have h1 : r • (1 : B) = r • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact hr
  exact one_ne_zero (hreg h1)

theorem stalk_of_smooth_over_regular :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p →
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x) ∧
        (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧
        Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  intro R _ _ X p hp x
  haveI : Smooth p := hp
  haveI : IsRegularRing (CommRingCat.of R) := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p x
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  have hRdom : IsDomain R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1
  have hfl : (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat := by
    haveI := flat_fromSpecStalk' X x
    have h : Flat (Spec.map (Spec.preimage (X.fromSpecStalk x ≫ p))) := by
      rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  refine ⟨hdom, inferInstance, hint, hfl, ?_⟩
  exact injective_of_flat_of_isDomain (A := R) _ hfl

end GlobalTheory.SmoothStalkNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickening
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

open MvPolynomial in
theorem mvPolynomial_map_pderiv_lift {κ R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (i : κ)
    (f : MvPolynomial κ R) :
    MvPolynomial.map π (pderiv i f) = pderiv i (MvPolynomial.map π f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, map_X, pderiv_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, Ne.symm h]

theorem isUnit_of_isUnit_map_of_sqZero_ker {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = 0) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this


open MvPolynomial in
theorem standardSmooth_lift_of_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hB₀
  obtain ⟨κ, τ, _, _, ⟨P⟩⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsemi : SemiHom π p := by
    intro r b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h0
      rw [hp, hφ] at h0
      have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
        rw [P.span_range_relation_eq_ker]
        first
          | exact h0
          | exact RingHom.mem_ker.mpr h0
          | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
      let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
      have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
      have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
        simp [hc', hv]
      rw [MvPolynomial.ker_map, hk] at hg
      have hs : ∑ j, c' j * v j ∈ J :=
        Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
      rw [this]
      have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
      rwa [Ideal.map_map] at hmm
    · intro hb
      have : I.map (algebraMap R (MvPolynomial κ R ⧸ J)) ≤ RingHom.ker p := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, halg]
        have : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        simp [this]
      exact this hb
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ (fun a ha => (hker a).1 ha) _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have := Q'.isStandardSmooth
  exact ⟨_, inferInstance, inferInstance, p, hsemi, hsurj, hker, inferInstance⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymBaseChange

theorem inv_left_fst (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) :
    (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left ≫ pullback.fst G.hom j =
      pullback.fst G.hom j ≫ (GrpObj.inv : G ⟶ G).left := by
  exact pullback.lift_fst _ _ _

theorem symm_pull : ∀ (S T : Scheme.{0}) (G : Over S) [GrpObj G] (j : T ⟶ S) (L : LB G.left), L.IsLB → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso ((L.pull (pullback.fst G.hom j)).pull (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left) (L.pull (pullback.fst G.hom j)) := by
  intro S T G _ j L hL h
  have e := inv_left_fst S T G j
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom j) (GrpObj.inv : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom j) e
  have h3 := GenSpread.lbIso_pullback h (pullback.fst G.hom j)
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymBaseChange
end

