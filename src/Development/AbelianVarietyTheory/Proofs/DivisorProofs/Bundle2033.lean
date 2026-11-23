module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResGInjectiveOfTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.TupleBundle

theorem resG_injective_of_top {X : Scheme.{0}} {V : X.Opens} (h : ⊤ ≤ V) : Function.Injective (resG X h) := by
  obtain rfl : V = ⊤ := top_unique h
  have e : (homOfLE h : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  intro a b hab
  simpa [resG, e] using hab

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)) :
    resG X h2 (resG X h1 a) = resG X (h2.trans h1) a := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h2 : W ≤ V)
    (a : Γ(X, U)) : resG Y h2 ((f.appLE U V h).hom a) = (f.appLE U W (h2.trans h)).hom a := by
  show (f.appLE U V h ≫ Y.presheaf.map _).hom a = _
  rw [Scheme.Hom.appLE_map]

variable {Ω : Type} [Field Ω]

def ev (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Γ(Sp Ω, V) →+* Ω :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (resG (Sp Ω) hV)

theorem ev_injective (V : (Sp Ω).Opens) (hV : ⊤ ≤ V) : Function.Injective (ev V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.injective.comp (resG_injective_of_top hV)

theorem ev_resG {V W : (Sp Ω).Opens} (hV : ⊤ ≤ V) (hW : ⊤ ≤ W) (h : W ≤ V) (a : Γ(Sp Ω, V)) :
    ev W hW (resG (Sp Ω) h a) = ev V hV a := by
  simp only [ev, RingHom.comp_apply, resG_resG]

theorem ev_resG_top {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (x : Ω) :
    ev V hV (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x)) = x := by
  have e : (homOfLE (hV.trans le_top) : (⊤ : (Sp Ω).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  simp only [ev, RingHom.comp_apply, resG_resG]
  simp [resG, e]

theorem ev_appLE {X : Scheme.{0}} (x : Sp Ω ⟶ X) {U : X.Opens} {V : (Sp Ω).Opens} (hV : ⊤ ≤ V) (h : V ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : ev V hV ((x.appLE U V h).hom f) = valF x U f := by
  simp only [ev, RingHom.comp_apply, resG_appLE, valF, dif_pos (hV.trans h)]

end GlobalTheory.TupleBundle

namespace GlobalTheory.TupleBundle

theorem exists_lb_of_hasDiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (J : Type)
    [Finite J] (v : J → Ω), M.HasDiv v → ∃ (δ : LB M.Z) (t : J → δ.Sec), δ.IsLB ∧ (⨆ a, nonzeroLocus (t a)) = ⊤ ∧
    (∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z) ∧ ZM.SecCoord δ t M.pt v := by
  intro o Ω _ _ _ M J _ v hv
  let U : {a // v a ≠ 0} → M.Z.Opens := fun k => ⟨{z | M.Div v k.1 z}, M.isOpen_setOf_div v k.1⟩
  have hU : ⨆ k, U k = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi.1⟩, hi⟩
  obtain ⟨g, hLB, hGT⟩ := ZH.RatModel.exists_isLB_genTriv_of_ratios o Ω M {a // v a ≠ 0} U (fun k => v k.1) hU
    (fun k => k.2) (fun k k' z hz => hz.1.2 k'.1)
  let δ : LB M.Z := ⟨{a // v a ≠ 0}, U, g⟩
  have hsec : ∀ a, ∃ σ : δ.Sec, M.HasVal (H := δ) (fun k => v k.1) σ (v a) := fun a =>
    hGT.exists_sec_hasVal (v a) fun k z hz => hz.2 a
  choose t ht using hsec
  have hnz : ∀ a z, z ∈ nonzeroLocus (t a) ↔ M.Div v a z := by
    intro a z
    simp only [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨k, hk⟩
      have hzk : z ∈ U k := M.Z.basicOpen_le _ hk
      have hval : valF M.pt (U k) ((t a).f k) = v a / v k.1 := ht a k ⟨z, hzk⟩
      have hu := (ZH.RatModel.isUnit_valF_iff (M := M) hzk ((t a).f k)).2 hk
      rw [ZH.RatModel.isUnit_O_iff] at hu
      simp only [hval] at hu
      obtain ⟨h1, h2⟩ := hu
      have hk0 := k.2
      have ha0 : v a ≠ 0 := (div_ne_zero_iff.1 h1).1
      refine ⟨ha0, fun j => ?_⟩
      have e : v j / v a = (v j / v k.1) * (v a / v k.1)⁻¹ := by field_simp
      rw [e]
      exact mul_mem (hzk.2 j) h2
    · intro h
      refine ⟨⟨a, h.1⟩, ?_⟩
      have hzk : z ∈ U ⟨a, h.1⟩ := h
      rw [← ZH.RatModel.isUnit_valF_iff (M := M) hzk, ZH.RatModel.isUnit_O_iff]
      have hv1 : valF M.pt (U ⟨a, h.1⟩) ((t a).f ⟨a, h.1⟩) = 1 := (ht a ⟨a, h.1⟩ ⟨z, hzk⟩).trans (div_self h.1)
      simp only [hv1, inv_one]
      exact ⟨one_ne_zero, one_mem _⟩
  refine ⟨δ, t, hLB, ?_, hnz, ?_⟩
  · refine top_unique fun z _ => ?_
    obtain ⟨i, hi⟩ := hv z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hnz i z).2 hi⟩
  · have hgen : ∀ k : {a // v a ≠ 0}, ⊤ ≤ M.pt ⁻¹ᵁ U k := fun k w _ => by
      show M.pt w ∈ U k
      rw [M.pt_apply w]
      exact ZH.RatModel.div_genericPoint (M := M) k.2
    have hW : ∀ j, ⊤ ≤ (δ.pull M.pt).U j := fun j w _ =>
      Set.mem_iInter.2 fun _ => hgen (j PUnit.unit) (x := w) trivial
    let τ : (δ.pull M.pt).Gen := ⟨fun j => Units.map (resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤)).toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom.toMonoidHom
        (Units.mk0 (v (j PUnit.unit).1)⁻¹ (inv_ne_zero (j PUnit.unit).2)))⟩
    have hτ : ∀ j, ((τ.s j : Γ(Sp Ω, (δ.pull M.pt).U j)ˣ) : Γ(Sp Ω, (δ.pull M.pt).U j)) =
        resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹) := fun j => rfl
    refine ⟨τ, fun j j' => ?_, fun i j h => ?_⟩
    · have hle : (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' ≤ M.pt ⁻¹ᵁ (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) :=
        le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ => M.pt) j PUnit.unit))
          (inf_le_right.trans (LB.wchart_le δ (fun _ => M.pt) j' PUnit.unit))
      have e0 : (δ.pull M.pt).g j j' = Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) :=
        (Fintype.prod_unique fun _ : PUnit.{1} =>
          Semi.res hle (pullU M.pt _ (δ.g (j PUnit.unit) (j' PUnit.unit))) ^ (1 : ℤ)).trans (zpow_one _)
      have hne : ((U (j PUnit.unit) ⊓ U (j' PUnit.unit) : M.Z.Opens) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2,
          ZH.RatModel.div_genericPoint (M := M) (j' PUnit.unit).2⟩
      have hg := hGT.g_eq (j PUnit.unit) (j' PUnit.unit) hne
      have hV : ⊤ ≤ (δ.pull M.pt).U j ⊓ (δ.pull M.pt).U j' := le_inf (hW j) (hW j')
      refine Units.ext (ev_injective _ hV ?_)
      rw [e0]
      show ev _ hV (resG (Sp Ω) inf_le_left (τ.s j : Γ(Sp Ω, _))) =
        ev _ hV ((M.pt.appLE _ _ hle).hom (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) *
          resG (Sp Ω) inf_le_right (τ.s j' : Γ(Sp Ω, _)))
      rw [map_mul, ev_resG (hW j), ev_resG (hW j'), ev_appLE, hτ, hτ, ev_resG_top, ev_resG_top]
      have h1 := (j PUnit.unit).2
      have h2 := (j' PUnit.unit).2
      have hg' : valF M.pt (U (j PUnit.unit) ⊓ U (j' PUnit.unit)) (δ.g (j PUnit.unit) (j' PUnit.unit) : Γ(M.Z, _)) =
          v (j' PUnit.unit).1 / v (j PUnit.unit).1 := hg
      rw [hg']
      field_simp
    · have hne : (U (j PUnit.unit) : Set M.Z).Nonempty :=
        ⟨genericPoint M.Z, ZH.RatModel.div_genericPoint (M := M) (j PUnit.unit).2⟩
      have hv' : valF M.pt (U (j PUnit.unit)) ((t i).f (j PUnit.unit)) = v i / v (j PUnit.unit).1 :=
        ht i (j PUnit.unit) hne
      refine ev_injective _ (hW j) ?_
      simp only [map_mul, hτ]
      rw [ev_appLE, ev_resG_top]
      change _ = v i * ev _ (hW j) (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (v (j PUnit.unit).1)⁻¹))
      rw [ev_resG_top, hv', div_eq_mul_inv]

end GlobalTheory.TupleBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := _root_.GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := _root_.GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameRigidifiedFamilyAbelianSchemeOfLocal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.SameLocal

theorem injective_app_of_section {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (V : Y.Opens) : Function.Injective (p.app V).hom := by
  have hi : IsIso ((e ≫ p).app V) := by
    rw [Scheme.Hom.congr_app he V]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (Functor.map_isIso _ _)
  have k : ∀ z, ((e ≫ p).app V).hom z = (e.app (p ⁻¹ᵁ V)).hom ((p.app V).hom z) := fun z => rfl
  intro x x' hx
  apply (ConcreteCategory.bijective_of_isIso ((e ≫ p).app V)).1
  change ((e ≫ p).app V).hom x = ((e ≫ p).app V).hom x'
  rw [k, k, hx]

theorem same_of_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U T : Over (Sp R)) (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) (hM : M.IsLB) (hN : N.IsLB), (∀ (Y : Over (Sp R)) (u : Y ⟶ U), evc hM (1 : Y ⟶ A) u = 0) → (∀ (Y : Over (Sp R)) (t : Y ⟶ T), evc hN (1 : Y ⟶ A) t = 0) → ∀ (Y : Over (Sp R)) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ Same A M N (Over.homMk W.ι rfl ≫ u : Over.mk (W.ι ≫ Y.hom) ⟶ U) (Over.homMk W.ι rfl ≫ t)) → Same A M N u t := by
  intro R _ _ A _ hA U T M N hM hN hMr hNr Y u t hloc
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [p, e, ← Over.comp_left, lift_snd, Over.id_left]
  have hp : ∀ V : Y.left.Opens, Function.Bijective (p.app V).hom := fun V =>
    ⟨injective_app_of_section p e he V,
      GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns _ (Out.TLinPf.isAb_pullback Y.hom A hA) V⟩
  rw [same_iff hM hN, ← sub_eq_zero]
  obtain ⟨L, hL, hLc⟩ := cls_surj (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t))
  have hloc' : ∀ y : Y.left, ∃ V : Y.left.Opens, y ∈ V ∧ ∃ g : LB.Gen (L.pull (p ⁻¹ᵁ V).ι), g.IsGen := by
    intro y
    obtain ⟨W, hyW, hW⟩ := hloc y
    refine ⟨W, hyW, (cls_eq_zero_iff (pull_isLB hL _)).1 ?_⟩
    rw [cls_pull hL, hLc]
    let j : Over.mk (W.ι ≫ Y.hom) ⟶ Y := Over.homMk W.ι rfl
    have h0 : CechPic.pull (A ◁ j).left
        (evc hM (fst A Y) (snd A Y ≫ u) - evc hN (fst A Y) (snd A Y ≫ t)) = 0 := by
      rw [map_sub, pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc, sub_eq_zero]
      exact (same_iff hM hN _ _).1 hW
    let P : Over (Sp R) := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ Y).hom)
    let k : P ⟶ A ⊗ Y := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let w : P ⟶ Over.mk (W.ι ≫ Y.hom) := Over.homMk (IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr) (by
      simp only [Over.mk_hom, P]
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Over.w (snd A Y)])
    let φ : P ⟶ A ⊗ Over.mk (W.ι ≫ Y.hom) := lift (k ≫ fst A Y) w
    have hφ : φ ≫ (A ◁ j) = k := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc]
        exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    have e2 : (p ⁻¹ᵁ W).ι = φ.left ≫ (A ◁ j).left := by rw [← Over.comp_left, hφ]; rfl
    rw [e2, pull_comp, h0, map_zero]
  obtain ⟨N', hN', w, hw⟩ := GlobalTheory.CubeLawCompare.iso_pull_of_locally_trivial p hp hL hloc'
  have h1 : CechPic.pull p (cls N' hN') = cls L hL := by
    rw [← cls_pull hN' p (pull_isLB hN' p)]
    exact (cls_eq_iff _ hL).2 ⟨w, hw⟩
  have h2 : CechPic.pull e (cls L hL) = 0 := by
    rw [hLc, map_sub, pull_evc, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp, hMr, hNr, sub_zero]
  have h3 : cls N' hN' = 0 := by
    rw [← h2, ← h1, ← pull_comp, he, pull_id]
  rw [← hLc, ← h1, h3, map_zero]

end GlobalTheory.DualCon.SameLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem secMaps_secPull_of_pointwise : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LL.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ) (LM.pull fst)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k) →
    ∀ (th : LP.Sec) (σ : LL.Sec) (σ' : LM.Sec),
      (∀ (j : (LL.pull φ).ι) (i : LP.ι) (h : (LL.pull φ).U j ⊓ LP.U i ≤ φ ⁻¹ᵁ LL.U (j PUnit.unit)),
        (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
          (show Γ(XA, (LL.pull φ).U j ⊓ LP.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (th.f i)) →
      GlobalTheory.Cartier.SecMaps e σ' σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull th θ) (GlobalTheory.Cartier.secPull σ' fst) := by
  intro Y XA XG θ φ fst hfst LP LL LM hLL ψ e w₀ hw th σ σ' hth he
  subst hfst
  rintro ⟨J, K⟩
  apply fn_ext
  intro y hy
  have hj : (θ ≫ φ) y ∈ LM.U (J PUnit.unit) := mem_pull.1 hy.1
  have hk : θ y ∈ LP.U (K PUnit.unit) := mem_pull.1 hy.2
  obtain ⟨i, hi⟩ := exists_chart hLL ((θ ≫ φ) y)
  have hm1 : (θ ≫ φ) y ∈ LL.U i ⊓ LM.U (J PUnit.unit) := ⟨hi, hj⟩
  have hm2 : θ y ∈ (LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit) := ⟨mem_pull.2 hi, hk⟩
  have ha := congrArg (gs (θ ≫ φ) y (LL.U i ⊓ LM.U (J PUnit.unit))) (he (i, J PUnit.unit))
  have hb := congrArg (gs θ y ((LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit)))
    (hth (fun _ => i) (K PUnit.unit) (inf_le_left.trans fun x hx => mem_pull.1 hx))
  have hc := hw Y (𝟙 Y) y i (J PUnit.unit) (K PUnit.unit) hi hj hk
  simp only [Category.id_comp] at hc
  rw [gs_mul _ y _ hm1, gs_unit _ y _ hm1] at ha
  change gs _ y _ (resG XG _ _) = _ * gs _ y _ (resG XG _ _) at ha
  rw [gs_res _ y _ hm1, gs_res _ y _ hm1] at ha
  dsimp only at hb
  erw [gs_mul _ y _ hm2, gs_unit _ y _ hm2] at hb
  change _ = _ * gs _ y _ (resG XA _ _) at hb
  rw [gs_res _ y _ hm2] at hb
  have hb' : gs (θ ≫ φ) y (LL.U i) (σ.f i) =
      (gw ψ θ y i (K PUnit.unit)).val * gs θ y (LP.U (K PUnit.unit)) (th.f (K PUnit.unit)) :=
    (gs_pull θ φ y _ hi _).symm.trans ((gs_res θ y _ hm2 _).symm.trans hb)
  have hm3 : (𝟙 Y) y ∈ (LM.pull (θ ≫ φ)).U J := hy.1
  have hm4 : (𝟙 Y) y ∈ (LP.pull θ).U K := hy.2
  change gs (𝟙 Y) y _ (resG Y _ (resG Y _ _)) = _
  erw [gs_res _ y _ hy, gs_res _ y _ hm3, gs_pull (𝟙 Y) (θ ≫ φ) y _ hj, gs_mul _ y _ hy, gs_unit _ y _ hy]
  change _ = _ * gs (𝟙 Y) y _ (resG Y _ (resG Y _ _))
  erw [gs_res _ y _ hy, gs_res _ y _ hm4, gs_pull (𝟙 Y) θ y (LP.U (K PUnit.unit)) hk]
  simp only [Category.id_comp]
  change _ = (gw w₀ (𝟙 Y) y (J PUnit.unit) fun _ => K PUnit.unit).val * _
  rw [hc, Units.val_mul, _root_.mul_assoc, ← hb']
  dsimp only [id] at ha
  rw [ha, Units.inv_mul_cancel_left]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDvrFormallyUnramifiedOfEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_restrict_dvr_comap_dominatesStalk : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ (V : ValuationSubring M.functionField) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap (functionFieldMap f))], DominatesStalk V z → letI := ((functionFieldMap f).restrict (V.comap (functionFieldMap f)) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap (functionFieldMap f)) V := by
  first | exact @GlobalTheory.trace_dvr_formallyUnramified_of_etale | exact GlobalTheory.trace_dvr_formallyUnramified_of_etale | (intros; apply GlobalTheory.trace_dvr_formallyUnramified_of_etale <;> assumption)
end

