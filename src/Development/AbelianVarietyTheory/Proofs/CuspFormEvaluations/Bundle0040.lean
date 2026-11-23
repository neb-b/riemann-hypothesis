module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

noncomputable section

namespace GlobalTheory.ChartFrames

section Alg

variable {S Ix : Type} [CommRing S]

theorem nilpotent_of_le (m : ℕ) (I : Ideal (Jet S Ix m))
    (h : ∀ p : MvPolynomial Ix S, Ideal.Quotient.mk _ p ∈ I → p ∈ orig S Ix) : IsNilpotent I := by
  refine ⟨m + 1, le_bot_iff.1 ?_⟩
  have h1 : I ≤ Ideal.map (Ideal.Quotient.mk (orig S Ix ^ (m + 1))) (orig S Ix) := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.mem_map_of_mem _ (h p ha)
  refine (Ideal.pow_right_mono h1 _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem trunc_surj (m : ℕ) :
    Function.Surjective ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem trunc_nil (m : ℕ) : IsNilpotent
    (RingHom.ker ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m)) :=
  nilpotent_of_le _ _ fun p hp => by
    have : Ideal.Quotient.mk (orig S Ix ^ (m + 1)) p = 0 := hp
    exact Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.Quotient.eq_zero_iff_mem.1 this)

theorem aug_surj (m : ℕ) : Function.Surjective ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S) :=
  fun a => ⟨algebraMap S _ a, (jetAug : Jet S Ix m →ₐ[S] S).commutes a⟩

theorem aug_nil (m : ℕ) : IsNilpotent (RingHom.ker ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S)) :=
  nilpotent_of_le _ _ fun p hp => by
    have h1 : MvPolynomial.aeval (fun _ => (0 : S)) p = 0 := hp
    have h2 : MvPolynomial.constantCoeff p = 0 := by simpa using h1
    simpa [h2] using sub_const_mem_orig p

variable (d : ℕ)

theorem aug_axis0 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis0 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem aug_axis1 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis1 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem trunc_axis0 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis0 d (m + 1)) =
    (axis0 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem trunc_axis1 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis1 d (m + 1)) =
    (axis1 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem aug_trunc (m : ℕ) : (jetAug : Jet S Ix m →ₐ[S] S).comp (jetTrunc : Jet S Ix (m + 1) →ₐ[S] _) = jetAug := by
  apply jet_hom_ext
  intro p
  rfl

theorem cancel₀ {U : Type} [CommGroup U] (a b : U) : a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [mul_right_comm a, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem cancel₁ {U : Type} [CommGroup U] (a b : U) : a * a⁻¹ * b⁻¹ * b = 1 := by
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem exists_norm {T : Over X0} (p q : T ⟶ t.G) (s₁ s₂ s₀ : T ⟶ T)
    (h₁ : s₁ ≫ (p * q) = p) (h₂ : s₂ ≫ (p * q) = q) (h₀ : s₀ ≫ (p * q) = 1)
    (g₁ : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (p * q).left) (fun _ => 1))) (hg₁ : g₁.IsGen) :
    ∃ e : LB.Gen (LB.LinComb t.PP.L (cφG t ![p, q]) (cε 2)), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good t.PP.L z J →
        val e r z J = val g₁ r z J * (val g₁ (r ≫ s₁.left) z J)⁻¹ * (val g₁ (r ≫ s₂.left) z J)⁻¹ *
          val g₁ (r ≫ s₀.left) z J := by
  obtain ⟨e, he, hv⟩ := exists_gen t.PP.isLB (φ' := cφG t ![p, q]) (ε' := cε 2) (fun U _ h => by
      have hc := prod_cube2 t.G (fun w : T ⟶ t.G => h w.left) ![p, q]
      refine Eq.trans ?_ hc.symm
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, h₁, h₂, h₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, zpow_neg, zpow_one]
      ac_rfl)
    (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ g₁
      (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₁.left))) (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₂.left)))
      (LB.pullGen t.PP.L _ _ g₁ s₀.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg₁
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _))) (DVR.pullGen_isGen _ _ _ _ hg₁ _))
  refine ⟨e, he, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem exists_tower {Ix : Type} (P : ∀ m, overAt x0 (Jet S Ix m) ⟶ t.G)
    (h0 : Formalism.L2.Pj.homAt x0 (jetAug : Jet S Ix 0 →ₐ[S] S) ≫ P 0 = 1)
    (htr : ∀ m, Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) ≫ P (m + 1) = P m) :
    ∃ g₁ : ∀ m, LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)), (∀ m, (g₁ m).IsGen) ∧
      ∀ m (Z : Scheme.{0}) (r : Z ⟶ (overAt x0 (Jet S Ix m)).left) (z : Z) (J), Good t.PP.L z J →
        val (g₁ (m + 1)) (r ≫ (Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m)).left) z J =
          val (g₁ m) r z J := by
  obtain ⟨g0, hg0, -⟩ := GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix 0) S _ (aug_surj 0) (aug_nil 0)
    PUnit.{1} (fun _ => (P 0).left) (fun _ => 1) PUnit.{1} (fun _ => (overAt x0 S).hom ≫ eSec t.G) (fun _ => 1)
    (LB.pullGen t.PP.L (fun _ : PUnit.{1} => eSec t.G) (fun _ => 1) t.PP.rig (overAt x0 S).hom)
    (DVR.pullGen_isGen _ _ _ _ t.PP.rigGen _) (fun U _ h => by
      have := congrArg Over.Hom.left h0
      exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  have step := fun m (g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1))) (hg : g.IsGen) =>
    GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix (m + 1)) (Jet S Ix m) _ (trunc_surj m) (trunc_nil m)
      PUnit.{1} (fun _ => (P (m + 1)).left) (fun _ => 1) PUnit.{1} (fun _ => (P m).left) (fun _ => 1) g hg
      (fun U _ h => by
        have := congrArg Over.Hom.left (htr m)
        exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  choose f hf hc using step
  let g₁ : ∀ m, {g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)) // g.IsGen} :=
    fun m => Nat.rec ⟨g0, hg0⟩ (fun m g => ⟨f m g.1 g.2, hf m g.1 g.2⟩) m
  refine ⟨fun m => (g₁ m).1, fun m => (g₁ m).2, fun m Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (hc m (g₁ m).1 (g₁ m).2) r)

end Geo

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch

  let c : ∀ m, Fin 2 → (jOG x0 d m 2 ⟶ jOG x0 d m 1) := fun m i => Formalism.L2.Pj.homAt x0 (jetCopy d m i)
  let a0 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis0 d m)
  let a1 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis1 d m)
  let o : ∀ m n, overAt x0 S ⟶ jOG x0 d m n := fun m n => Formalism.L2.Pj.homAt x0 jetAug
  let u : ∀ m n, jOG x0 d m n ⟶ overAt x0 S := fun m n => Formalism.L2.Pj.homAt x0 (Algebra.ofId S _)
  let tr : ∀ m n, jOG x0 d m n ⟶ jOG x0 d (m + 1) n := fun m n => Formalism.L2.Pj.homAt x0 jetTrunc
  have a0c0 : ∀ m, a0 m ≫ c m 0 = u m 1 ≫ o m 1 := fun m => by
    simp only [a0, c, u, o, homAt_comp, first_axis_at_first_copy]
  have a0c1 : ∀ m, a0 m ≫ c m 1 = 𝟙 _ := fun m => by
    simp only [a0, c, homAt_comp, first_axis_at_second_copy, homAt_id]
  have a1c0 : ∀ m, a1 m ≫ c m 0 = 𝟙 _ := fun m => by
    simp only [a1, c, homAt_comp, second_axis_at_first_copy, homAt_id]
  have a1c1 : ∀ m, a1 m ≫ c m 1 = u m 1 ≫ o m 1 := fun m => by
    simp only [a1, c, u, o, homAt_comp, second_axis_at_second_copy]
  have oa0 : ∀ m, o m 1 ≫ a0 m = o m 2 := fun m => by
    simp only [a0, o, homAt_comp, aug_axis0]
  have oa1 : ∀ m, o m 1 ≫ a1 m = o m 2 := fun m => by
    simp only [a1, o, homAt_comp, aug_axis1]
  have oc : ∀ m i, o m 2 ≫ c m i = o m 1 := fun m i => by
    simp only [c, o, homAt_comp, aug_copy]
  have a0u : ∀ m, a0 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a0, u, homAt_comp, Algebra.comp_ofId]
  have a1u : ∀ m, a1 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a1, u, homAt_comp, Algebra.comp_ofId]
  have tru : ∀ m, tr m 2 ≫ u (m + 1) 2 = u m 2 := fun m => by
    simp only [tr, u, homAt_comp, Algebra.comp_ofId]
  have otr : ∀ m, o m 2 ≫ tr m 2 = o (m + 1) 2 := fun m => by
    simp only [tr, o, homAt_comp, aug_trunc]
  have trc : ∀ m i, tr m 2 ≫ c (m + 1) i = c m i ≫ tr m 1 := fun m i => by
    simp only [tr, c, homAt_comp, copy_trunc]
  have tra0 : ∀ m, tr m 1 ≫ a0 (m + 1) = a0 m ≫ tr m 2 := fun m => by
    simp only [tr, a0, homAt_comp, trunc_axis0]
  have tra1 : ∀ m, tr m 1 ≫ a1 (m + 1) = a1 m ≫ tr m 2 := fun m => by
    simp only [tr, a1, homAt_comp, trunc_axis1]
  have ox : ∀ m, o m 1 ≫ x m = 1 := hch.zero
  have trx : ∀ m, tr m 1 ≫ x (m + 1) = x m := hch.trunc
  have hj : ∀ m i, jptG t x0 d x m i = c m i ≫ x m := fun _ _ => rfl
  obtain ⟨g₁, hg₁, hg₁t⟩ := exists_tower t x0
    (fun m => jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2))
    (by
      change o 0 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (oc 0), ox, _root_.mul_one])
    (fun m => by
      change tr m 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (trc m), trx])
  have key := fun m => exists_norm t (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))
    (c m 0 ≫ a1 m) (c m 1 ≫ a0 m) (u m 2 ≫ o m 2)
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), ox,
      MonObj.comp_one, _root_.mul_one])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), ox,
      MonObj.comp_one, _root_.one_mul])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (oc m), ox, MonObj.comp_one, _root_.mul_one])
    (g₁ m) (hg₁ m)
  choose e he hv using key
  refine ⟨e, he, fun m => corr_of_val t.PP.isLB fun y J hJ => ?_, fun m => ⟨corr_of_val t.PP.isLB fun y J hJ => ?_,
    corr_of_val t.PP.isLB fun y J hJ => ?_⟩⟩
  · refine (val_pull hJ _ _ _).trans ((hv (m + 1) _ _ y J hJ).trans (Eq.trans ?_ (hv m _ _ y J hJ).symm))
    have e1 : ∀ (s : jOG x0 d m 2 ⟶ jOG x0 d m 2) (s' : jOG x0 d (m + 1) 2 ⟶ jOG x0 d (m + 1) 2),
        tr m 2 ≫ s' = s ≫ tr m 2 →
        val (g₁ (m + 1)) ((𝟙 _ ≫ (tr m 2).left) ≫ s'.left) y J = val (g₁ m) (𝟙 _ ≫ s.left) y J := by
      intro s s' hs
      rw [Category.assoc, ← Over.comp_left, hs, Over.comp_left, ← Category.assoc]
      exact hg₁t m _ _ y J hJ
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (hg₁t m _ _ y J hJ)
      (congrArg _ (e1 _ _ ?_))) (congrArg _ (e1 _ _ ?_))) (e1 _ _ ?_)
    · simp only [Category.assoc, reassoc_of% (trc m), tra1]
    · simp only [Category.assoc, reassoc_of% (trc m), tra0]
    · simp only [Category.assoc, reassoc_of% (tru m), otr]
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a0 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), reassoc_of% (a0u m), oa1]
    exact cancel₀ _ _
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a1 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), reassoc_of% (a1u m), oa0]
    exact cancel₁ _ _

end GlobalTheory.ChartFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TranslExist

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ L.wchart φ j ↔ ∀ k, φ k y ∈ L.U (j k) := by
  unfold LB.wchart
  show y ∈ (⋂ k, (φ k) ⁻¹' (L.U (j k) : Set X)) ↔ _
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]

theorem twist_congr (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (h : ∀ y J, Good L y J → val α (𝟙 _) y J = val α' (𝟙 _) y J) {s : LB.Sec (LPow A L b T)}
    {s' s'' : LB.Sec (LPow A L a T)} (h' : IsTwistPull A L ψ m hm a b α s s')
    (h'' : IsTwistPull A L ψ m hm a b α' s s'') : s' = s'' := by
  unfold IsTwistPull at h' h''
  have hf : ∀ i, s'.f i = s''.f i := by
    intro i
    obtain ⟨i0, rfl⟩ : ∃ i0 : L.ι, i = (fun _ : Fin 1 => i0) := ⟨i 0, funext fun k => by fin_cases k; rfl⟩
    apply fn_ext
    intro x hx
    have hx0 : (snd T A).left x ∈ L.U i0 :=
      (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) x).mp hx 0
    obtain ⟨j1, hj1, hj1'⟩ : ∃ j1 : L.ι, m.left x ∈ L.U j1 ∧ (m.left = (snd T A).left → j1 = i0) := by
      by_cases e : m.left = (snd T A).left
      · exact ⟨i0, by rw [e]; exact hx0, fun _ => rfl⟩
      · have hc : m.left x ∈ (⨆ k, L.U k) := by rw [hL.cover]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
        exact ⟨k, hk, fun h => absurd h e⟩
    let j : Fin 2 → L.ι := ![i0, j1]
    have hxW : x ∈ L.wchart ![(snd T A).left, m.left] j := by
      rw [mem_wchart_lemma]
      intro k
      fin_cases k
      · exact hx0
      · exact hj1
    obtain ⟨J, hJ, hJk⟩ := exists_good L hL x ![(snd T A).left, m.left] j (by
      intro p q hpq
      fin_cases p <;> fin_cases q
      · rfl
      · exact (hj1' hpq.symm).symm
      · exact hj1' hpq
      · rfl) (by
      intro k
      fin_cases k
      · exact hx0
      · exact hj1)
    have hv := h x J hJ
    rw [val_of α (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k),
      val_of α' (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k)] at hv
    have hle : L.wchart ![(snd T A).left, m.left] j ≤ (LPow A L a T).U (fun _ : Fin 1 => i0) := by
      intro y hy
      exact (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) y).mpr
        (fun _ => (mem_wchart_lemma L _ j y).mp hy 0)
    have e1 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h' j)
    have e2 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h'' j)
    rw [gs_mul _ _ _ hxW] at e1 e2
    have hu : gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α.s j).val =
        gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α'.s j).val := by
      exact (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α.s j)).trans
        ((congrArg Units.val hv).trans (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α'.s j)).symm)
    have r1 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s'.f fun _ => i0)
    have r2 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s''.f fun _ => i0)
    exact r1.symm.trans (e1.trans ((congrArg (· * _) hu).trans (e2.symm.trans r2)))
  obtain ⟨f1, p1⟩ := s'
  obtain ⟨f2, p2⟩ := s''
  have : f1 = f2 := funext hf
  subst this
  rfl

theorem act_congr (hL : L.IsLB) {T : Over S} {k : ℤ} {U U' : ThetaGrp A L k T} (hp : U.pt = U'.pt)
    (h : LB.Gen.Corr L _ _ _ _ U.φ U'.φ) {s s' s'' : LB.Sec (LPow A L k T)} (h' : IsActOf A L k U s s')
    (h'' : IsActOf A L k U' s s'') : s' = s'' := by
  obtain ⟨pt, φ, hφ⟩ := U
  obtain ⟨pt', φ', hφ'⟩ := U'
  simp only at hp
  subst hp
  unfold IsActOf at h' h''
  exact twist_congr hL (fun y J hJ => val_corr hJ h (𝟙 _)) h' h''

end TranslExist


open TranslExist in
theorem exists_isVtOver_and_existsUnique_isUUOver : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  intro hLaws E _ _ _ H Dw l Xo N hN T s
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨α₀, hg₀, hn₀, hu₀, hT⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hLaws E H Dw l Xo N
  obtain ⟨α, hgα, hcα⟩ := hT T
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G T N)
      (snd T Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ :=
    (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ α hgα s).exists
  have hact : ∀ (U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)
      (a : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)),
      ∃ b, IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U a b := by
    intro U a
    unfold IsActOf
    exact (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ U.φ U.isGen a).exists
  refine ⟨fun ok t t' h1 h2 h3 => ?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩
  · obtain ⟨U, hU⟩ := (_root_.GlobalTheory.moduli_univ_symLift_global hLaws E H Dw l Xo N hN T t' h2).1
    obtain ⟨F, hF⟩ := hact U s₁
    exact ⟨F, t', α₀, α, s₁, U, h1, h3, hg₀, hn₀, hcα, hs₁, hU, hF⟩
  · have S₁ := _root_.GlobalTheory.moduli_univ_symLift_global hLaws E H Dw l Xo N hN T x₁ hx₁
    have S₂ := _root_.GlobalTheory.moduli_univ_symLift_global hLaws E H Dw l Xo N hN T x₂ hx₂
    obtain ⟨U₁, hU₁⟩ := S₁.1
    obtain ⟨U₂, hU₂⟩ := S₂.1
    obtain ⟨s₂, hs₂⟩ := hact U₁ s₁
    obtain ⟨F, hF⟩ := hact U₂ s₂
    refine ⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, hg₀, hn₀, hcα, hs₁, hU₁, hs₂, hU₂, hF⟩, ?_⟩
    rintro F' ⟨β₀, β, t₁, t₂, V₁, V₂, hgβ₀, hnβ₀, hcβ, ht₁, hV₁, ht₂, hV₂, hF'⟩
    have e₁ : t₁ = s₁ := by
      refine twist_congr hL (fun y J hJ => ?_) ht₁ hs₁
      exact (val_corr hJ hcβ _).trans ((val_pull hJ β₀ _ _).trans ((val_corr hJ (hu₀ β₀ hgβ₀ hnβ₀) _).trans
        ((val_corr hJ hcα _).trans (val_pull hJ α₀ _ _)).symm))
    rw [e₁] at ht₂
    have e₂ : t₂ = s₂ :=
      act_congr hL (hV₁.pt_eq.trans hU₁.pt_eq.symm) (S₁.2 V₁ U₁ hV₁ hU₁) ht₂ hs₂
    rw [e₂] at hF'
    exact act_congr hL (hV₂.pt_eq.trans hU₂.pt_eq.symm) (S₂.2 V₂ U₂ hV₂ hU₂) hF' hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogThetaSum
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaSumLevi

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y Topology Filter

theorem levi_lower {n : ℕ} {ι : Type} (s : Finset ι) {g : ι → V n → ℂ} {D : V n → ℂ}
    {φ : V n → ℝ} {z : V n} (c d : ℝ) (hg : ∀ t, ContDiffAt ℂ 2 (g t) z) (hD : ContDiffAt ℂ 2 D z)
    (hD0 : D z ≠ 0) (hφ : ContDiffAt ℝ 2 φ z) (hpos : 0 < ∑ t ∈ s, Complex.normSq (g t z))
    (ξ : Fin n → ℂ) :
    -(c * (leviV n (fun w => ((φ w : ℝ) : ℂ)) z ξ).re) ≤
      (leviV n (fun w => ((Real.log (∑ t ∈ s, Complex.normSq (g t w)) +
        ((c * Real.log (Complex.normSq (D w)) + d) + (-c) * φ w) : ℝ) : ℂ)) z ξ).re := by
  have hS : ContDiffAt ℝ 2 (fun w => Real.log (∑ t ∈ s, Complex.normSq (g t w))) z :=
    (ContDiffAt.sum fun t _ => contDiffAt_normSq_comp (hg t)).log hpos.ne'
  have hL : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (D w))) z :=
    (contDiffAt_normSq_comp hD).log (Complex.normSq_pos.2 hD0).ne'
  have hL' : ContDiffAt ℝ 2 (fun w => c * Real.log (Complex.normSq (D w)) + d) z :=
    (contDiffAt_const.mul hL).add contDiffAt_const
  have hφ' : ContDiffAt ℝ 2 (fun w => (-c) * φ w) z := contDiffAt_const.mul hφ
  have e : ∀ w, ∑ t ∈ s, Complex.normSq (g t w) =
      ∑ i : Fin s.card, Complex.normSq (g (s.equivFin.symm i) w) := fun w => by
    rw [← Finset.sum_coe_sort s]
    exact (s.equivFin.symm.sum_comp fun t => Complex.normSq (g t w)).symm
  have h0 := leviV_log_sum_nonneg (u := fun (i : Fin s.card) w => Complex.normSq (g (s.equivFin.symm i) w))
    (x := z) (fun i => contDiffAt_normSq_comp (hg _)) (fun i => logPshAt_normSq (hg _))
    (by rw [← e]; exact hpos) ξ
  simp only [← e] at h0
  rw [LocalMaximumSecondDerivative.leviV_ofReal_add hS (hL'.add hφ'), LocalMaximumSecondDerivative.leviV_ofReal_add hL' hφ',
    leviV_const_mul hL, leviV_log_normSq hD hD0, LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ hφ]
  simp only [mul_zero, zero_add, Complex.add_re, Complex.re_ofReal_mul]
  linarith

theorem levi_log_theta_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → ∀ x0 ∈ X.dom, ∀ z, cpt X.toData x0 z ∈ X.dom → ∀ ξ : Fin (nd X.toData) → ℂ, -((r : ℝ) / 2 * leviM X.toData (phla X.toData (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1)) x0 z ξ) ≤ leviM X.toData ps x0 z ξ := by
  intro E _ _ _ r X _ hw ps hps x0 _ z hz ξ
  obtain ⟨Θ, D, κ, hκ, hΘ, hD, hD0, hval⟩ := GlobalTheory.ThetaHol.normalised_theta_norm_holomorphic E r X hw
  obtain ⟨𝒯, h1, h2⟩ := GlobalTheory.LevelTupleSum.exists_reps X.Λ X.Λ_fg
  set la : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1 with hla
  have hO := ExF.isOpen_OmF X.toData x0
  have hz' : z ∈ OmF X.toData x0 := hz
  have hc : Differentiable ℂ (cpt X.toData x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X.toData x0 τ a b).differentiable (by simp)
  have hhol : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ P X.dom →
      ContDiffAt ℂ 2 (fun w => P (cpt X.toData x0 w)) z := fun hP =>
    contDiffAt_two_of_holo hO (hP.comp hc.differentiableOn fun _ hw => hw) hz'
  have key : ∀ w ∈ OmF X.toData x0,
      0 < ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w)) ∧
      ps (cpt X.toData x0 w) = Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) := by
    intro w hw
    have hN : 0 < X.nfac la (cpt X.toData x0 w) := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X.toData x0 hw
    have hx : cpt X.toData x0 w ∈ X.dom := hw
    generalize cpt X.toData x0 w = x at hN hx
    obtain ⟨A, hA⟩ := hps x hx
    have hp := GlobalTheory.TupleSumPos.tuple_sum_pos E r X x A
    have hs := GlobalTheory.LevelTupleSum.sum_eq hx A 𝒯 h1 h2 _ (GlobalTheory.LevelTupleSum.torus_r A)
    rw [hs] at hA hp
    have hDp : 0 < ‖D x‖ := norm_pos_iff.2 (hD0 x hx)
    have hK : 0 < (κ * ‖D x‖ * X.nfac la x) ^ r := by positivity
    have e : ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s =
        (κ * ‖D x‖ * X.nfac la x) ^ r * ∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hval x hx A, Complex.normSq_eq_norm_sq]
      ring
    rw [e] at hA hp
    have hS := (mul_pos_iff_of_pos_left hK).1 hp
    refine ⟨hS, ?_⟩
    rw [hA, Real.log_mul hK.ne' hS.ne', Real.log_pow, Real.log_mul (by positivity) hN.ne',
      Real.log_mul hκ.ne' hDp.ne', IW.log_norm_eq, phla]
    ring
  have hev : (fun w => ((ps (cpt X.toData x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w =>
      ((Real.log (∑ t ∈ 𝒯, Complex.normSq (∏ b, Θ (t b) (cpt X.toData x0 w))) +
        (((r : ℝ) / 2 * Real.log (Complex.normSq (D (cpt X.toData x0 w))) + r * Real.log κ) +
          (-((r : ℝ) / 2)) * phla X.toData la (cpt X.toData x0 w)) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hz'] with w hw
    rw [(key w hw).2]
  unfold leviM
  rw [leviV_congr hev]
  exact levi_lower 𝒯 (g := fun t w => ∏ b, Θ (t b) (cpt X.toData x0 w)) _ _
    (fun t => contDiffAt_prod fun b _ => hhol (hΘ _)) (hhol hD) (hD0 _ hz)
    ((IW.phla_cpt_cdAt X.toData x0 hz' la).of_le (by norm_cast)) (key z hz').1 ξ

end GlobalTheory.ThetaSumLevi
end

