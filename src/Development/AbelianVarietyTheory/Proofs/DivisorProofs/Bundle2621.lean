module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmooth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermLB

open Set GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPos_pull_of_genSmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    L.SemiPos D → (L.pull π hπ).SemiPos E := by
  intro k _ X Y p q D E hX π hπ L hL σ
  obtain ⟨R⟩ := hX σ
  intro i c y hy ξ
  set φ := L.φ σ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨a, h0⟩ := R.cover (m y)
  set c0 := R.chart a
  have him : m y ∈ ptsIn p σ (L.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V E → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn E _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c0 h0 him)
  have e : (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  show 0 ≤ (leviV E (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp E D g F U hU _ hyU hF hg ξ, hFy]
  exact hL σ (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.HermLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomChartConstantCoeffSubst
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem semiHom_constantCoeff_and_ev : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, (s.app 0).counit_map, c.aug, map_zero]
  refine ⟨hconst, fun n g => ?_⟩
  have hy : ∀ j, IsNilpotent (s.app n (c.x n j)) := fun j => (c.nil n j).map (s.app n).toRingHom
  have h1 := (_root_.GlobalTheory.evA_subst_and_map k' (Fin d) (G'.A n)).1 (Fin e) (c'.ev n)
    (fun t => by
      change IsNilpotent (evA k' (c'.x n) (c'.nil n) (X t))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c'.nil n t) φ hconst _ hy (fun j => hφ n j) (MvPowerSeries.map σ g)
  rw [h1]
  letI : Algebra k (G'.A n) := ((algebraMap k' (G'.A n)).comp σ).toAlgebra
  let S : G.A n →ₐ[k] G'.A n :=
    { (s.app n).toRingHom with commutes' := fun r => (s.app n).map_algebraMap r }
  have h2 := (_root_.GlobalTheory.evA_subst_and_map k (Fin d) (G.A n)).2 (G'.A n) S (c.x n) (c.nil n) _ hy (fun _ => rfl) g
  change _ = S (evA k (c.x n) (c.nil n) g)
  rw [h2]
  let M : MvPowerSeries (Fin d) k →ₐ[k] G'.A n :=
    { (evA k' _ hy : MvPowerSeries (Fin d) k' →+* G'.A n).comp (MvPowerSeries.map σ) with
      commutes' := fun r => by
        change evA k' _ hy (MvPowerSeries.map σ (algebraMap k _ r)) = algebraMap k' _ (σ r)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.map_C, ← (evA k' _ hy).commutes (σ r), MvPowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hM : M = evA k _ hy := _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k (Fin d) (G'.A n) M _
    (fun i => by
      change IsNilpotent (evA k' _ hy (MvPowerSeries.map σ (X i)))
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact hy i)
    (fun i => by
      change evA k' _ hy (MvPowerSeries.map σ (X i)) = _
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate])
  exact AlgHom.congr_fun hM g

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem semiHom_ev₂_pull2 : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ n t
  have hev := _root_.GlobalTheory.EvSquare.main p k' e G' c' n
  let a : Fin d ⊕ Fin d → MvPowerSeries (Fin e ⊕ Fin e) k' :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))
  have ha : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    have hc := hev.2.2.2
    cases i with
    | inl j =>
      change constantCoeff (inL (φ j)) = 0
      rw [← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
    | inr j =>
      change constantCoeff (inR (φ j)) = 0
      rw [← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change Coalgebra.counit (R := k') (c'.ev n (φ j)) = 0
      rw [hφ n j, (s.app n).counit_map, c.aug, map_zero]
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  let B := G'.A n ⊗[k'] G'.A n
  letI : Algebra k B := ((algebraMap k' B).comp σ).toAlgebra
  let u : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeLeft : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeft (R := k') (S := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let v : G.A n →ₐ[k] B :=
    { ((Algebra.TensorProduct.includeRight : G'.A n →ₐ[k'] B) : G'.A n →+* B).comp
        (s.app n).toRingHom with
      commutes' := fun r => by
        change Algebra.TensorProduct.includeRight (R := k') ((s.app n) (algebraMap k (G.A n) r)) = _
        rw [(s.app n).map_algebraMap, AlgHom.commutes]; rfl }
  let T : G.A n ⊗[k] G.A n →ₐ[k] B := Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)
  have hT : ∀ z, T z = (s.app n).two z := fun z => by
    induction z with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul x y =>
      rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul]
      change ((s.app n) x ⊗ₜ[k'] 1) * (1 ⊗ₜ[k'] (s.app n) y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₐ[k] B :=
    { (c'.ev₂ n).toRingHom.comp
        ((substAlgHom (R := k') hs).toRingHom.comp
          (MvPowerSeries.map σ)) with
      commutes' := fun r => by
        change c'.ev₂ n (substAlgHom (R := k') hs (MvPowerSeries.map σ (C r))) = algebraMap k' B (σ r)
        rw [MvPowerSeries.map_C, show (C (σ r) : MvPowerSeries (Fin d ⊕ Fin d) k') =
          algebraMap k' _ (σ r) by rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
          AlgHom.commutes, AlgHom.commutes] }
  have hL : ∀ f, L f = c'.ev₂ n (pull2 φ (MvPowerSeries.map σ f)) := fun f => by
    change c'.ev₂ n (substAlgHom hs (MvPowerSeries.map σ f)) = _
    rw [coe_substAlgHom]; rfl
  have key : T.comp (c.ev₂ n) = L := by
    refine _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k (Fin d ⊕ Fin d) B _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply]
      change IsNilpotent (T (evA k (c.x₂ n) (c.nil₂ n) (X i)))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact (c.nil₂ n i).map T
    · rw [AlgHom.comp_apply, hL, hT, MvPowerSeries.map_X]
      change (s.app n).two (evA k (c.x₂ n) (c.nil₂ n) (X i)) = c'.ev₂ n (subst a (X i))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, subst_X hs]
      cases i with
      | inl j =>
        change (s.app n).two (c.x n j ⊗ₜ 1) = c'.ev₂ n (inL (φ j))
        rw [hev.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
      | inr j =>
        change (s.app n).two (1 ⊗ₜ c.x n j) = c'.ev₂ n (inR (φ j))
        rw [hev.2.1, hφ n j, TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
        congr 1; exact map_one (s.app n).toRingHom
  rw [← hL, ← key, AlgHom.comp_apply, hT]

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem sharpRef_of_tens : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  intro W V _ _ Q V₁ _ _ ρ D₀ D e₀ hR T e he
  obtain ⟨β, β₂, wR, hpb, hsq, hwR, hcR, htR⟩ := hR
  obtain ⟨io, hιm, hι⟩ := grpPullback_iso hpb (isGrpPullback_pullback Q.B (spMap ρ))
  have hprI : ∀ a, IsMonHom (T.pr a ≫ io.hom) := fun a => by
    haveI := T.pr_hom a; haveI := hιm; infer_instance
  have hpr' : ∀ a, (T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = (T.pr a).left ≫ β := fun a => by
    rw [Over.comp_left, Category.assoc, hι]
  let φQ : (Fin 8 × Fin 8) × Fin 4 → (D.P.A.left ⟶ Q.B.left) := fun k =>
    lamPts (T.pr k.1.1 ≫ io.hom) (T.pr k.1.2 ≫ io.hom) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)
  let εQ : (Fin 8 × Fin 8) × Fin 4 → ℤ := fun k => -(W k.1.1 k.1.2 * negε k.2)
  obtain ⟨v, hv, hvv⟩ := _root_.GlobalTheory.Mum.LamBridge.exists_iso_tens D₀.P.A Q.B D₀.P.L Q.M.L D₀.P.isLB Q.M.isLB β₂ wR hwR W D.P.A T.pr φQ εQ
    (fun k => _root_.GlobalTheory.PairPts.lamPts_fst_eq_psum D₀.P.A Q.B (spMap ρ) β β₂ hpb hsq D.P.A _ _ _ _ (hpr' _) (hpr' _) k.2)
    (fun k => by obtain ⟨⟨a, b⟩, i⟩ := k; fin_cases i <;> simp [εQ, negε, Oε])
  obtain ⟨w', hw', hwv⟩ := _root_.GlobalTheory.IsoPullIdComp.exists_comp_val (A := D.P.L) (tensφ T.pr) (tensε W) φQ εQ D.P.isLB D₀.P.isLB Q.M.isLB T.w T.w_gen v hv
  refine ⟨fun a => T.pr a ≫ io.hom, w', hprI, fun T' y => ?_, hw', fun mu a => ?_, fun κ hκ mu z J J' hJ hJ' => ?_⟩
  · refine ⟨Fan.IsLimit.lift T.lim (fun a => y a ≫ io.inv), fun a => ?_, fun x hx => ?_⟩
    · have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      show _ ≫ T.pr a ≫ io.hom = _
      rw [← Category.assoc, h]
      simp
    · refine Fan.IsLimit.hom_ext T.lim _ _ fun a => ?_
      have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      change x ≫ T.pr a = _ ≫ T.pr a
      rw [h, ← hx a]
      simp
  · show (D.c (e mu) ≫ T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = _
    rw [← Category.assoc, Over.comp_left, Category.assoc, hι, T.c_pr, hcR, he]
  · choose J₀ hJ₀ using fun s : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (s z)
    have hJ₀' : Good D₀.P.L z J₀ := hJ₀
    have h1 := T.psi (e mu) z J₀ J' hJ₀' hJ'
    have h2 := hwv _ (D.xK (e mu)) z J J₀ (J' (D.xK (e mu))) (hJ' _) hJ hJ₀'
    have h3 := hvv _ (D.xK (e mu)) z J J₀ hJ hJ₀'
    have h4 : ∀ a b, D.xK (e mu) ≫ (lift (T.pr a) (T.pr b)).left =
        (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left := by
      intro a b
      show (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.assoc, Category.assoc, T.c_pr, T.c_pr]
    have h5 : ∀ a b, val (D₀.tau (T.xe (e mu) a) (T.xe (e mu) b)) (𝟙 _) z J₀ =
        lamVal wR (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left z J J₀ *
          val (Q.tau (mu a) (mu b)) κ z J := fun a b => by
      rw [htR κ hκ _ _ z J J₀ hJ hJ₀', he, he]
    rw [h1]
    erw [h2]
    rw [h3]
    simp only [h4, h5, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem eighthPowerFibre_thetaObj : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.e8_act_linComb_relAmple W hW
  obtain ⟨Mat, hMat⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.Lab.exists_symplectic_labels W hW gQ
  refine ⟨Fin 2, inferInstance, Mat, κ, 0, 1, ?_⟩
  intro l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q hQ ρ hρ D e hS K _ _ ev k₀ hk₀
  obtain ⟨P', ψ, B, _, M, pr, hg, hψ, hL, hB, hpr, hE, hpt⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists W gQ V V₁ Q hQ ρ hρ D e hS K ev
  haveI : IsCommMonObj B := hB.1.comm
  choose act hact1 hact2 using fun i : Fin 2 => _root_.GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy _ _ _ pr hpr (E8Fibration.actMat W i)
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨bT, pt, htor, hbij, hpair, hsh⟩ := hMat l hl hlo j hj K k₀ hk₀ hlK P' hg B M pr hB hpr hE act hact1 hact2
  let t : TObj (8 * gQ) ((l ^ j) ^ 2) (Fin 2) bT (spMap k₀.subtype) :=
    { A := P'.A, grp := P'.grp, ab := P'.isAb, dim := hg ▸ P'.smoothDim, L := P'.L, isLB := P'.isLB,
      rigid := P'.rigid, sym := P'.sym, ample := P'.ample, ktriv := P'.ktriv, pt := pt, torsion := htor,
      bij := hbij, pairing := hpair, act := act, hom := hact1 }
  refine ⟨bT, t, ψ, ?_, ?_, hψ, hL, ?_⟩
  · exact fun a => ⟨hsh a, hκ gQ K P' B M pr hB hpr hE act hact1 hact2 a⟩
  · exact GlobalTheory.T.e8_act_prod_eq_one W hW gQ K P' B M pr hB hpr hE act hact1 hact2
  · intro y hy q hq1 hq2
    obtain ⟨y', hy'1, hy'2⟩ := hpt _ y hy q hq1 hq2
    obtain ⟨c, hc, -⟩ := hbij K (𝟙 _) y' hy'2
    refine ⟨c, ?_⟩
    rw [← hy'1, ← hc]
    have h0 : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; simp
    simp only [h0, Category.id_comp]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemberZeta

open GlobalTheory.Points

theorem valR_through_stalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem val_germ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {V : Type} [CommRing V] [IsDomain V]
    {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V) (x : M.Z.presheaf.stalk z) :
    M.val (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V (FractionRing V) (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    have : (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w) this U.isOpen hz
  have e : jK V ≫ spMap ev = spMap ((algebraMap V (FractionRing V)).comp ev) := by
    rw [← Spec.map_comp]; rfl
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, e, valR_through_stalk _ hz]
  rfl

theorem algebraMap_ev_eq_yK : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) (z : X.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X.M.Z.presheaf.stalk z →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X z act V ev Y t δ) (zt : X.M.Z.presheaf.stalk z),
    X.M.stalkHom z zt = algebraMap X.o₁ X.Ω₁ X.S.ζ →
    algebraMap V (FractionRing V) (ev zt) = 𝔪.yK ⟨algebraMap X.o₁ X.Ω₁ X.S.ζ, X.S.R.algebraMap_mem _⟩ := by
  intro g n F W Z i X z act V _ _ _ ev Y _ m t δ 𝔪 zt h
  rw [𝔪.yK_eq]
  exact (val_germ ev zt).symm.trans (congrArg (X.M.val _) h)

end GlobalTheory.Poinc.Sep.MemberZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVarProj

theorem strHom_eq_and_isProjOver : ∀ (K : Type) [Field K] (A : AbVar K),
    (letI := A.algΓ; GlobalTheory.strHom K A.X.left = A.X.hom) ∧ IsProjOver A.X.hom := by
  intro K _ A
  refine ⟨?_, ?_⟩
  · letI := A.algΓ
    exact GlobalTheory.strHom_eq fun _ => rfl
  · exact (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.X.hom).1
      (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)

end GlobalTheory.AV.AbVarProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_functionFieldModelHom_of_projective : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z),
    X.IsHom M (AlgHom.id o Ω) f → IsProjOver M.s → Function.Surjective f := by
  first | exact @GlobalTheory.ProjModelSurj.surjective_of_isProjOver | exact GlobalTheory.ProjModelSurj.surjective_of_isProjOver | (intros; apply GlobalTheory.ProjModelSurj.surjective_of_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataFactorPairingPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_data_factor_pairing_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), (∃ w₁ : LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) (LB.LinComb D.toPre.P.L (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2) (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)), w₁.IsGen ∧ ∀ (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = gm (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z _ (w₁.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ GlobalTheory.PolDeg.lamPts (fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.1) (snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr k.1.2) k.2), fun I => J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) I.down).left))) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j)) → ∀ (i₀ : Fin r), letI := T.mod (symUnitOf W h); ∃ w : LB.Iso (abelian₂ D.toPre.P.A D.toPre.P.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull (lift (fst D.toPre.P.A D.toPre.P.A ≫ T.inc i₀) (snd D.toPre.P.A D.toPre.P.A ≫ T.inc i₀ ≫ T.act (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 D.toPre.P.A ⟶ G2 D'.toPre.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good D.toPre.P.L z J' → val (D.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.toPre.c a) (toUnit (TK R) ≫ D.toPre.c b)).left z J J' * val (D'.toPre.tau (T.xi i₀ a) (TensO.binv (symUnitOf W h) • T.xi i₀ b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.TensPair.pair_pull | exact GlobalTheory.TensPair.pair_pull | (intros; apply GlobalTheory.TensPair.pair_pull <;> assumption)
end

