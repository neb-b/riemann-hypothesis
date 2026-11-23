module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullPerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjSwap

section Charts

variable {X Y Y' : Scheme.{0}}

def pullInv {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso B A) :
    LB.Iso A' B' where
  s p := (res (fun y hy => ⟨a.le _ hy.2, b.le _ hy.1⟩ :
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)))
    (pullU h _ (w.s (a.idx p.2, b.idx p.1))))⁻¹

theorem gm_pullInv {Z : Scheme.{0}} {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (b : ChartPull B' B h) (w : LB.Iso B A) (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullInv a b w).s p) =
      (gm (r ≫ h) z (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans
    (gm_pull r h z _ (show h (r z) ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) from ⟨a.le _ hz.2, b.le _ hz.1⟩) _)))

theorem pullInv_isGen {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    {w : LB.Iso B A} (hw : w.IsGen) : (pullInv a b w).IsGen := fun p q => unit_ext fun y hy => by
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((pullInv a b w).s p) =
        (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ := fun p hp =>
    (gm_pullInv a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) :=
    ⟨⟨a.le _ hy.1.2, b.le _ hy.1.1⟩, ⟨a.le _ hy.2.2, b.le _ hy.2.1⟩⟩
  have e := congrArg (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1))))
    (hw (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1))
  have e' : gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)) =
      gm h y (A.U (a.idx p.2) ⊓ A.U (a.idx q.2)) (A.g (a.idx p.2) (a.idx q.2)) *
        (gm h y (B.U (b.idx p.1) ⊓ B.U (b.idx q.1)) (B.g (b.idx p.1) (b.idx q.1)))⁻¹ *
        gm h y (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) (w.s (a.idx q.2, b.idx q.1)) :=
    (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B A h y (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1) hm) (gm_res h y _ hm _))))
  have d : gm (𝟙 Y') y ((LB.div B' A').U p ⊓ (LB.div B' A').U q) ((LB.div B' A').g p q) =
      gm (𝟙 Y') y (B'.U p.1 ⊓ B'.U q.1) (B'.g p.1 q.1) * (gm (𝟙 Y') y (A'.U p.2 ⊓ A'.U q.2) (A'.g p.2 q.2))⁻¹ :=
    gm_div A' B' (𝟙 Y') y p q hy
  refine (gm_res _ y _ hy _).trans ((val p hy.1).trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  rw [d, gm_res (𝟙 Y') y _ hy, val q hy.2, b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, e']
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem gm_gen_congr {M : LB X} (t : LB.Gen M) {r r' : Y ⟶ X} (hr : r = r') (y : Y) {i i' : M.ι} (hi : i = i') :
    gm r y (M.U i) (t.s i) = gm r' y (M.U i') (t.s i') := by
  subst hr hi; rfl

theorem gm_g_congr (L : LB X) (f : Y ⟶ X) (y : Y) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') :
    gm f y (L.U i ⊓ L.U j) (L.g i j) = gm f y (L.U i' ⊓ L.U j') (L.g i' j') := by
  subst hi hj; rfl

def chartPullPerm (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : K ≃ K) (hc : ∀ k, φ' k = h ≫ φ (e k)) (hε : ∀ k, ε (e k) = ε k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j k := j (e.symm k)
  le j y hy := Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy (e.symm k)
    rw [hc, Equiv.apply_symm_apply] at this
    exact this
  g y j j' hj hj' := by
    refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_ (gm_linComb L φ ε h y _ _
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj' (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)).symm)
    refine Fintype.prod_equiv e _ _ fun k => ?_
    simp only [hε, Category.id_comp, hc]
    exact congrArg (· ^ ε k) (gm_g_congr L _ y (congrArg j (e.symm_apply_apply k)).symm
      (congrArg j' (e.symm_apply_apply k)).symm)

end Charts

section Sums

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I = ∏ i ∈ I, x i := by
  have hnd : ((List.finRange n).filter (· ∈ I)).Nodup := (List.nodup_finRange n).filter _
  calc psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
        unfold psum
        generalize ((List.finRange n).filter (· ∈ I)) = l
        induction l with
        | nil => rfl
        | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]; rfl
    _ = ∏ i ∈ I, x i := by
        rw [← List.prod_toFinset x hnd]
        congr 1
        ext i
        simp

theorem psum_perm {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G))
    (π : Equiv.Perm (Fin n)) (hx : ∀ i, x' i = σ ≫ x (π i)) (I : Finset (Fin n)) :
    psum G x' I = σ ≫ psum G x (I.map π.toEmbedding) := by
  calc psum G x' I = ∏ i ∈ I, x' i := psum_eq_prod x' I
    _ = ∏ i ∈ I, σ ≫ x (π i) := by simp only [hx]
    _ = σ ≫ ∏ i ∈ I, x (π i) := (map_prod (preHom (G := G) σ) _ I).symm
    _ = σ ≫ ∏ i ∈ I.map π.toEmbedding, x i := by rw [Finset.prod_map]; rfl
    _ = σ ≫ psum G x (I.map π.toEmbedding) := by rw [psum_eq_prod]

end Sums

def swapIdx : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).finsetCongr.trans Equiv.ulift.symm)

theorem swapIdx_down (I : ULift.{0} (Finset (Fin 2))) :
    (swapIdx I).down = I.down.map (Equiv.swap (0 : Fin 2) 1).toEmbedding := rfl

end GlobalTheory.MumFam.AdjSwap

namespace GlobalTheory.MumFam


open AdjSwap in
theorem adj_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₁ a' a h' h := by
  intro R _ _ Q₁ Q₂ a a' h h' ⟨ha, ha', hc, hc', w, hw, hv⟩
  let σ : Q₂.B ⊗ Q₁.B ⟶ Q₁.B ⊗ Q₂.B := lift (snd Q₂.B Q₁.B) (fst Q₂.B Q₁.B)
  have hA : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] K.down).left =
      σ.left ≫ (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hB : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] K.down).left =
      σ.left ≫ (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hε : ∀ K : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - (swapIdx K).down.card)) = (-1) ^ (2 - K.down.card) :=
    fun K => by rw [swapIdx_down, Finset.card_map]
  let cA : ChartPull (cubeLB Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] Q₁.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L) σ.left :=
    chartPullPerm Q₁.M.L _ _ _ σ.left swapIdx hA hε
  let cB : ChartPull (cubeLB Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] Q₂.M.L)
      (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) σ.left :=
    chartPullPerm Q₂.M.L _ _ _ σ.left swapIdx hB hε
  refine ⟨ha', ha, hc', hc, pullInv cA cB w, pullInv_isGen cA cB hw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hp : (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left ≫ σ.left =
      (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left := by
    rw [← Over.comp_left]; congr 1; simp [σ]
  have key : adjVal (pullInv cA cB w) (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left z J₁ J₂ =
      (adjVal w (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left z J₂ J₁)⁻¹ := by
    let p' := (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left
    have m₁ := hJ₁.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left) p'
    have m₂ := hJ₂.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left) p'
    have e1 := gm_pullInv cA cB w p' z
      (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left),
        fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)) ⟨m₁, m₂⟩
    have i₁ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] k.down).left := fun k => by
      rw [hA, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have i₂ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] k.down).left := fun k => by
      rw [hB, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have e2 := gm_gen_congr w hp z (Prod.ext (funext fun k => congrArg J₂ (i₁ k)) (funext fun k => congrArg J₁ (i₂ k)) :
      ((cA.idx (fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)),
        cB.idx (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left))) :
          (LB.div (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L)
            (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)).ι) =
        (fun I => J₂ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] I.down).left),
          fun I => J₁ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left)))
    exact e1.trans (congrArg (·⁻¹) e2)
  have o := hv y' y z J₂ J₁ hJ₂ hJ₁
  rw [Q₂.tau_symm (h y') y z J₁ hJ₁, Q₁.tau_symm y' (h' y) z J₂ hJ₂] at o
  rw [key, o, inv_mul_cancel_left]

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullChartDens

theorem chernDens_pull_of_chart : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w) := by
  intro k _ X Y p q σ D π hπ B φ hφ c c' H z hz
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (φ.pull π hπ).isLB z) PUnit.unit
  rw [AlgChart.chernDens, AlgChart.chernDens, c.hess_eq hφ hz' hj (mem_pick _ _), AlgChart.hess,
    AlgChart.hess, ← (H z hz).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (φ.pull_φ π hπ _ _)

end GlobalTheory.PullChartDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem chernMat_tens (L M : HermLB p) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    chernMat ((L.tens M).φ σ) c y = chernMat (L.φ σ) c y + chernMat (M.φ σ) c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  unfold chernMat
  rw [c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)]
  change c.hess ((L.φ σ).tens (M.φ σ)) _ y = _
  exact FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb

def chernHom (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    HermLB.IsomClass p →+ Matrix (Fin D) (Fin D) ℂ :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p)
    (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => chernMat (L.φ σ) c y)
    fun _ _ h => chernMat_congr h c hy) (by rintro ⟨L⟩ ⟨M⟩; exact chernMat_tens L M c hy)

theorem chernHom_icls (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) (L : HermLB p) :
    chernHom c hy L.icls = chernMat (L.φ σ) c y := rfl

theorem chernMat_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (κ : Type)
    [Fintype κ] (L : κ → HermLB p) (n : κ → ℤ) (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    chernMat ((ArInt.comb L n).φ σ) c y = ∑ j, (n j : ℂ) • chernMat ((L j).φ σ) c y := by
  intro k _ X p σ D κ _ L n c y hy
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← chernHom_icls c hy, icls_comb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, chernHom_icls, Int.cast_smul_eq_zsmul]

end GlobalTheory.MixDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

theorem chernMat_isForm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsForm fun (c : AlgChart p σ D) y => chernMat φ c y := by
  intro k _ X p σ D B φ hφ
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_, fun c y hy => ?_⟩
  · have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ChartGlue.mem_over c.e hy hy'
    have e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    unfold chernMat AlgChart.hess
    beta_reduce
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hφ.contDiffAt c' hy' (mem_pick _ y))), e₂, chg]
    have hJ : (Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l) =
        transMat c c' y := rfl
    rw [hJ]
    congr 1
  · intro v hv
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c.e.symm v))))
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c)
    have hc : ContinuousAt
        (fun w => cHess D (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ)) w) v :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
        (ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb ho hs a b).continuousAt (ho.mem_nhds hm)
    refine ContinuousAt.continuousWithinAt (hc.congr ?_)
    filter_upwards [ho.mem_nhds hm] with w hw
    unfold chernMat
    beta_reduce
    rw [c.hess_eq hφ (c.e.map_target hw.1) hw.2 (mem_pick _ _), AlgChart.hess, c.e.right_inv hw.1]
  · have hd := hφ.contDiffAt c hy (mem_pick φ.isLB y)
    set g : V D → ℂ := fun v => ((φ.φ (pick φ.isLB y) (c.e.symm v) : ℝ) : ℂ) with hg
    have hg2 : ContDiffAt ℝ 2 g (c.e y) := Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd
    have hgc : (fun w => (starRingEnd ℂ) (g w)) = g := funext fun w => by simp [g]
    show (cHess D g (c.e y)).IsHermitian
    ext j l
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wd D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y)) =
      ReciprocityTheory.L2DbarEstimates.wd D j (ReciprocityTheory.L2DbarEstimates.wdb D l g) (c.e y)
    have h1 : (fun w => (starRingEnd ℂ) (ReciprocityTheory.L2DbarEstimates.wdb D j g w)) = ReciprocityTheory.L2DbarEstimates.wd D j g := by
      funext w
      rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' D j g w, hgc]
    rw [← ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj' D l (ReciprocityTheory.L2DbarEstimates.wdb D j g) (c.e y), h1,
      ReciprocityTheory.L2DbarEstimates.comm_wd_wdb g (c.e y) hg2 j l]

end GlobalTheory.MixDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ChernNull

open Set CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_poly_dvd {k R : Type} [CommRing k] [IsDomain k] [CommRing R] [IsDomain R] {D : ℕ}
    (f : MvPolynomial (Fin D) k →+* R) (hf : f.Etale) (g : R) (hg : g ≠ 0) :
    ∃ Q : MvPolynomial (Fin D) k, Q ≠ 0 ∧ ∃ r : R, f Q = g * r := by
  letI := f.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) k) R := hf
  obtain ⟨Q, hQ, r, hr⟩ := (WeilIntegral.isAlgebraic_of_etale (MvPolynomial (Fin D) k) R g).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hg)
  exact ⟨Q, hQ, r, hr⟩

theorem analyticAt_eval {D : ℕ} (P : MvPolynomial (Fin D) ℂ) (z : Fin D → ℂ) :
    AnalyticAt ℂ (fun w : Fin D → ℂ => MvPolynomial.eval w P) z := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z)

theorem volume_poly_zero (D : ℕ) (P : MvPolynomial (Fin D) ℂ) (hP : P ≠ 0) :
    volume {v : ReciprocityTheory.L2DbarEstimates.V D | MvPolynomial.eval (fun a => v a) P = 0} = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ
    (fun z _ => analyticAt_eval P z) ⟨w, mem_univ _, hw⟩
  have hs : {z : Fin D → ℂ | z ∈ univ ∧ MvPolynomial.eval z P = 0} =
      {z : Fin D → ℂ | MvPolynomial.eval z P = 0} := by
    ext z
    simp
  have hT : MeasurableSet {z : Fin D → ℂ | MvPolynomial.eval z P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  rw [hs] at h0
  rw [← (volume_preserving_ofLp_complex (Fin D)).measure_preimage hT.nullMeasurableSet] at h0
  refine measure_mono_null (fun v hv => ?_) h0
  exact hv

theorem injective_of_arithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) (σ : k →+* ℂ) : Function.Injective σ := by
  have := h.isDomain
  have := h.finite
  have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker])
  refine (injective_iff_map_eq_zero σ).2 fun a ha => ?_
  have : a ∈ RingHom.ker σ := ha
  rwa [hk, Ideal.mem_bot] at this

theorem exists_sec_vanish {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z) :
    ∃ g : Γ(X, U), g ≠ 0 ∧ ∀ z ∈ U, z ∈ Z → z ∉ X.basicOpen g := by
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
  let W : X.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨g, hgW, hgm⟩ := hU.exists_basicOpen_le (V := W) ⟨genericPoint X, ⟨hgU, hgen⟩⟩ hgU
  refine ⟨g, fun e => ?_, fun z _ hz hzg => (hgW hzg).2 hz⟩
  rw [e, X.basicOpen_zero] at hgm
  exact hgm

theorem chart_null {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (h : IsArithVar p D) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z)
    (σ : k →+* ℂ) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  have := h.isDomain
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (injective_of_arithVar h σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem chernPart_over_closed : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X _ p D h Z hZ hgen σ B φ ε
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => chart_null h hZ hgen σ c

end GlobalTheory.ChernNull
end
end

