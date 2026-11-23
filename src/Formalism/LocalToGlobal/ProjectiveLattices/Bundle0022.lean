module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HolSubMul
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


set_option maxHeartbeats 400000 in
theorem frame_of_gen (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S))
    (m1 : SABMap t' Xo.univ.t x) (σ' : LB.Sec t'.PP.L)
    (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : S, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ (s : LB.Sec (PPx x)) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)),
      RigIso m1 w1 ∧ IsoMaps w1 σ' s1 ∧
      (∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
      ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w1, hw1, hrig, -⟩ := m1.lin
  have hPG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w1).1 hw1
  obtain ⟨s1, hs1⟩ := thf_secUp hPG Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have pb := m1.cart.1
  have hcond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
      h ≫ t'.G.hom = (fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨pb.lift _ _ hcond, pb.lift_fst _ _ hcond, pb.lift_snd _ _ hcond⟩
  obtain ⟨g0, g0F, g0S, hhg⟩ : ∃ g0 : t'.G.left ⟶ Gx x, g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ ∧
      g0 ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ h ≫ g0 = 𝟙 _ := by
    let P : Over Xo.X := Over.mk (m1.φ ≫ Xo.univ.t.G.hom)
    let a : P ⟶ Over.mk x := Over.homMk t'.G.hom pb.w.symm
    let b : P ⟶ Xo.univ.t.G := Over.homMk m1.φ rfl
    let hO : (Over.mk x ⊗ Xo.univ.t.G) ⟶ P := Over.homMk h (by
      show h ≫ m1.φ ≫ Xo.univ.t.G.hom = _
      rw [← Category.assoc, hF]
      exact Over.w (snd (Over.mk x) Xo.univ.t.G))
    have e : hO ≫ lift a b = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        ext
        exact hS
      · rw [Category.assoc, lift_snd, Category.id_comp]
        ext
        exact hF
    exact ⟨(lift a b).left, congrArg (fun f => f.left) (lift_snd (f := a) (g := b)),
      congrArg (fun f => f.left) (lift_fst (f := a) (g := b)), congrArg (fun f => f.left) e⟩
  have hgh0 : g0 ≫ h = 𝟙 _ := pb.hom_ext
    (by rw [Category.assoc, hF, g0F, Category.id_comp])
    (by rw [Category.assoc, hS, g0S, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s1, w1, s1, ⟨hw1, hrig⟩, ?_, ?_, ?_⟩
  · intro i k
    refine fn_ext fun y hy => ?_
    have key := hs1 _ (𝟙 _) y i k hy.1 hy.2
    rw [gs_res (𝟙 _) y _ hy, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
    congr 1
    exact (gs_unit (𝟙 _) y _ hy (w1.s (i, k))).symm
  · intro g hgs hgf j hj
    have hgh : g ≫ h = 𝟙 _ := pb.hom_ext
      (by rw [Category.assoc, hF, hgs, Category.id_comp])
      (by rw [Category.assoc, hS, hgf, Category.id_comp])
    refine fn_ext fun y hy => ?_
    have e1 := gs_appLE g _ _ hj (𝟙 _) y hy ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit))
    have e2 : gs g y ((PPx x).U (fun _ => j PUnit.unit)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit)) =
        gs (g ≫ h) y _ (s1.f (fun _ => j PUnit.unit)) :=
      gs_appLE h _ _ _ g y (hj hy) _
    rw [Category.id_comp] at e1
    rw [e1, e2, hgh]
    all_goals rfl
  · intro s''
    have hle : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := by
      intro j y hy
      have e : (g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
        rw [g0F]
        exact hy
      show g0.base y ∈ (⋂ k : Fin 1, ((snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U j : Set _)))
      exact Set.mem_iInter.2 fun _ => e
    have mm : ∀ (y : t'.G.left) j, m1.φ y ∈ Xo.univ.t.PP.L.U j → g0 y ∈ (PPx x).U (fun _ => j) :=
      fun y j hj => hle j hj
    have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.φ y ∈ Xo.univ.t.PP.L.U j →
        m1.φ y ∈ Xo.univ.t.PP.L.U j' →
        gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          (gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
            gs (𝟙 _) y _ ((g0.appLE _ _ (hle j')).hom (s''.f (fun _ => j'))) := by
      intro y j j' hj hj'
      have e1 := gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj) (s''.f (fun _ => j))
      have e2 := gs_appLE g0 _ _ (hle j') (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j' from hj')
        (s''.f (fun _ => j'))
      have e3 := gs_compat s'' g0 y (mm y j hj) (mm y j' hj')
      have e4 := gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        g0 y (fun _ => j) (fun _ => j') (mm y j hj) (mm y j' hj')
      simp only [Fin.prod_univ_one, zpow_one, g0F] at e4
      rw [e1, e2, Category.id_comp, e3]
      erw [e4]
    obtain ⟨σ'', hσ''⟩ := sec_down hPG Xo.univ.t.PP.isLB t'.PP.isLB
      (fun j => (g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) hσ
    obtain ⟨a, ha, hau⟩ := hgen σ''
    refine ⟨a, fun i => ?_, fun b hb => hau b ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim _ _)⟩
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ : ∃ k, h y ∈ t'.PP.L.U k := by
        have : h y ∈ ⨆ i, t'.PP.L.U i := by
          rw [t'.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have hF' : m1.φ (h y) ∈ Xo.univ.t.PP.L.U j := by
        have e : (h ≫ m1.φ) y ∈ Xo.univ.t.PP.L.U j := by
          rw [hF]
          exact LB.wchart_le Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
        exact e
      have eR1 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst (fst (Over.mk x) Xo.univ.t.G).left y a := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
        rw [Category.id_comp] at this
        exact this
      have eR2 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          (gw w1 h y j k).val * gs h y _ (σ'.f k) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (s1.f (fun _ => j))
        rw [Category.id_comp] at this
        exact this.trans (hs1 _ h y (fun _ => j) k (mem_pull.2 hF') hk)
      have eL : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 h y j k).val * (cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k)) := by
        have e5 := gs_appLE g0 _ _ (hle j) h y (show h y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hF') (s''.f (fun _ => j))
        rw [hhg] at e5
        rw [← e5, hσ'' _ h y j k hF' hk, ha k, gs_mul h y _ hk, gs_constFn t'.G.hom _ h y hk a, hS]
      rw [gs_mul (𝟙 _) y _ hy, eR1, eR2, eL, mul_left_comm]
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ : ∃ j, m1.φ y ∈ Xo.univ.t.PP.L.U j := by
        have : m1.φ y ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
          rw [Xo.univ.t.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have e1 := hσ'' _ (𝟙 _) y j k hj hy
      have c1 : gs g0 y _ (scal x b (fun _ => j)) = cst t'.G.hom y b := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) g0 y (mm y j hj) b
        rw [g0S] at this
        exact this
      have c2 : gs g0 y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          gs (𝟙 _) y _ (s1.f (fun _ => j)) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) g0 y (mm y j hj) (s1.f (fun _ => j))
        rw [hgh0] at this
        exact this
      have e2 : gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          cst t'.G.hom y b * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        rw [gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj), Category.id_comp,
          hb (fun _ => j), gs_mul g0 y _ (mm y j hj), c1, c2, hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy]
      have e3 := e1.symm.trans e2
      rw [mul_left_comm] at e3
      rw [gs_mul (𝟙 _) y _ hy, gs_constFn t'.G.hom _ (𝟙 _) y hy b, Category.id_comp]
      exact (Units.mul_right_inj (gw w1 (𝟙 _) y j k)).1 e3

theorem pull_sec {R S : Type} [CommRing R] [CommRing S] (G : SAB H (Sp R)) (t' : SAB H (Sp S)) {f : Sp S ⟶ Sp R}
    (m2 : SABMap t' G f) (θ : LB.Sec G.PP.L) :
    ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L),
      RigIso m2 w2 ∧ IsoMaps w2 σ' (thfPull G.PP.L m2.φ θ) := by
  obtain ⟨w2, hgen, hrig, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w2).1 hgen) G.PP.isLB t'.PP.isLB θ
  refine ⟨w2, σ', ⟨hgen, hrig⟩, fun i k => fn_ext fun y hy => ?_⟩
  have h1 : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  have key := hσ' _ (𝟙 _) y (i PUnit.unit) k h1 hy.2
  have hl : gs (𝟙 _) y _ ((thfPull G.PP.L m2.φ θ).f i) = gs (𝟙 _ ≫ m2.φ) y _ (θ.f (i PUnit.unit)) :=
    gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _
  rw [gs_res (𝟙 _) y _ hy, hl, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
  congr 1
  exact (gs_unit (𝟙 _) y _ hy (w2.s (i, k))).symm

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def RdIndep (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU (U σ) (b i))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem holSub_mul (hM : SiegelSpaceAlgebra (E := E)) {Comp : Type} {X : Comp → Data E r} {la la' : ∀ k, Wt (X k).Ψ r}
    {P Q : FDSec X} (hP : P ∈ holSub X la) (hQ : Q ∈ holSub X la') : P * Q ∈ holSub X (la + la') := by
  first | exact UpperTheory.Reformulated.B.Qe28.holSub_mul .. | (apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP hQ | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E

theorem cusp_mul_of_M5 (hM : SiegelSpaceAlgebra (E := E)) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMul Xo c U := by
  intro a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hd.2 hd'.2 k
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, hla]
  exact holSub_mul hM (hf.2 σ hσ) (hg.2 σ hσ)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DatIndep
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NabUniq : Prop :=
  ∀ (_ : StarRing (𝓞 E)) (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ a n, Dom a n → thGen Xo c nab a n = thGen Xo c nab' a n

def DatIndep : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw Tw' : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → PointsOfFlagModel.TowerAt Tw' →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io), OverLa la T.V io e → algCls Xo c T io y →
      ∀ z z', LiesOverBaseChange la Tw T io y z → LiesOverBaseChange la Tw' T io y z' →
        ∀ (A : DatAt (Tw.Y z.1) z.2.2.1) (A' : DatAt (Tw'.Y z'.1) z'.2.2.1),
          ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}


set_option maxHeartbeats 400000 in
theorem gfp_gen_of {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwg, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hwg
  obtain ⟨su, hsu⟩ := thf_secUp hw Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have hpb : IsPullback m1.cm.F t'.G.hom Xo.univ.t.G.hom x := And.left m1.cart
  obtain ⟨h, hF, hπ⟩ : ∃ h : Gx x ⟶ t'.G.left,
      h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧
        h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨hpb.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm), hpb.lift_fst _ _ _,
      hpb.lift_snd _ _ _⟩
  obtain ⟨k, hkφ, hkπ⟩ : ∃ k : t'.G.left ⟶ Gx x,
      k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F ∧
        k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom :=
    ⟨(CartesianMonoidalCategory.lift (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
      (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)).left,
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_snd
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)),
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_fst
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G))⟩
  have hkh : k ≫ h = 𝟙 _ := hpb.hom_ext (by rw [Category.assoc, hF, hkφ, Category.id_comp])
    (by rw [Category.assoc, hπ, hkπ, Category.id_comp])
  have hhk : h ≫ k = 𝟙 _ := by
    have e1 : (Over.homMk (h ≫ k) (by
        rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)]
        simp only [Category.assoc]
        rw [reassoc_of% hkπ, reassoc_of% hπ]) :
        Over.mk x ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G) = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkπ, hπ]
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkφ, hF]
    exact congrArg (fun f => Over.Hom.left f) e1
  have hscal : ∀ (b : L) (i : (PPx x).ι),
      scal x b i = constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U i) b :=
    fun _ _ => rfl
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    intro j y hy
    have e : (k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
      rw [hkφ]; exact hy
    show k y ∈ (PPx x).U (fun _ => j)
    exact Set.mem_iInter.2 fun _ => e
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF su, fun s'' => ?_⟩
  have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.cm.F y ∈ Xo.univ.t.PP.L.U j →
      m1.cm.F y ∈ Xo.univ.t.PP.L.U j' →
      gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        (gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
          gs (𝟙 _) y _ ((k.appLE _ _ (hle j')).hom (s''.f fun _ => j')) := fun y j j' h1 h2 =>
    (gs_appLE k _ _ (hle j) (𝟙 _) y h1 _).trans ((gs_compat s'' (𝟙 _ ≫ k) y (hle j h1) (hle j' h2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ((gm_linComb Xo.univ.t.PP.L
        (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        (𝟙 _ ≫ k) y (fun _ => j) (fun _ => j') (hle j h1) (hle j' h2)).trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hkφ])))
        (gs_appLE k _ _ (hle j') (𝟙 _) y h2 _).symm))
  obtain ⟨s', hs'⟩ := sec_down hw Xo.univ.t.PP.isLB t'.PP.isLB
    (fun j => (k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) hσ
  obtain ⟨a, ha, hau⟩ := hgen s'
  refine ⟨a, fun i => ?_, fun b hb => hau b fun k' => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine fn_ext fun y hy => ?_
    have hφy := LB.wchart_le Xo.univ.t.PP.L
      (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
    have hFy : m1.cm.F (h y) ∈ Xo.univ.t.PP.L.U j := by
      have e : (h ≫ m1.cm.F) y ∈ Xo.univ.t.PP.L.U j := by rw [hF]; exact hφy
      exact e
    obtain ⟨k', hk'⟩ : ∃ k', h y ∈ t'.PP.L.U k' := by
      have : h y ∈ (⨆ k', t'.PP.L.U k') := by rw [t'.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hL : gs (𝟙 _) y _ (s''.f fun _ => j) = (gw w h y j k').val *
        (cst (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k')) := by
      have e0 : gs (𝟙 (Gx x)) y ((PPx x).U fun _ => j) (s''.f fun _ => j) =
          gs (h ≫ k) y ((PPx x).U fun _ => j) (s''.f fun _ => j) := by rw [hhk]
      rw [e0, ← gs_appLE k _ _ (hle j) h y hFy, hs' _ h y j k' hFy hk', ha k', gs_mul h y _ hk',
        gs_constFn _ _ h y hk' a, hπ]
    rw [hL, gs_mul (𝟙 _) y _ hy]
    erw [hscal]
    rw [gs_constFn _ _ (𝟙 _) y hy a, Category.id_comp, mul_left_comm]
    congr 1
    symm
    refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (su.f fun _ => j)).trans ?_
    rw [Category.id_comp]
    exact hsu _ h y (fun _ => j) k' (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy) hk'
  · refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y ∈ Xo.univ.t.PP.L.U j := by
      have : m1.cm.F y ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by rw [Xo.univ.t.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hky : k y ∈ (PPx x).U (fun _ => j) := hle j hj
    have hd := hs' _ (𝟙 _) y j k' hj hy
    have hL : gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        cst t'.G.hom y b * ((gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ'.f k')) := by
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, Category.id_comp, hb (fun _ => j), gs_mul k y _ hky]
      erw [hscal]
      rw [gs_constFn _ _ k y hky b, hkπ]
      congr 1
      refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) k y hky (su.f fun _ => j)).trans ?_
      rw [hkh]
      exact hsu _ (𝟙 _) y (fun _ => j) k' (Set.mem_iInter.2 fun _ => hj) hy
    rw [gs_mul (𝟙 _) y _ hy, gs_constFn _ _ (𝟙 _) y hy b, Category.id_comp]
    apply (Units.mul_right_inj (gw w (𝟙 _) y j k')).1
    exact hd.symm.trans (hL.trans (by ring))

theorem gfp_gen (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {L : Type} [Field L] (x : Sp L ⟶ Xo.X) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨PP', cub, sym, adj, prim, m1, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Xo.univ.t
  obtain ⟨σ', hgen⟩ := globalSections_rank_one_fibre hT amplePt Xo.univ m1
  exact gfp_gen_of x m1 σ' hgen

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HeckeJ
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace HeckeJ

open scoped TensorProduct

section Gen

variable {L : Type*} [Field L] (σ₀ : L →+* ℂ) {WL : Type*} [AddCommGroup WL] [Module L WL]
  {H F : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup F] [Module ℂ F]
  (j : WL →ₛₗ[σ₀] H) (em : H →ₗ[ℂ] F) (TF : F →ₗ[ℂ] F) (c : ℂ)

def IsHkJ (T : WL →ₗ[L] WL) : Prop := ∀ x, em (j (T x)) = c • TF (em (j x))


variable {σ₀ j em TF c}

variable (σ₀ j em TF c)

variable {σ₀ j em TF c}

end Gen

section Inj

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

end Inj

end HeckeJ

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntAll
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def IntAll : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → T.FinRes →
    ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
      ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧
        letI := io.toAlgebra; letI := io'.toAlgebra
        ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
          (∀ a : T.V, φ (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ∧ FrMap φ y z ∧ FrBor t z y'.1

end Formalism.L2.Pj
end
end

