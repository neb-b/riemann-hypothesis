module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem exists_pullSec (a : ℤ) {T T' : Over S0} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s', IsPullSec A L a h hh s s' := by
  have hl : ∀ j, (LPow A L a T').U j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j := fun j => chart_le_res A L h hh a j
  have hc : h.left ≫ (snd T A).left = (snd T' A).left := by
    rw [← Over.comp_left, hh]
  refine ⟨⟨fun j => ((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j)), ?_⟩,
    fun j => rfl⟩
  intro j j'
  apply fn_ext
  intro y hy
  have v : ∀ j, y ∈ (LPow A L a T').U j →
      gs (𝟙 _) y _ (((T' ⊗ A).left.presheaf.map (homOfLE (hl j)).op).hom ((h.left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ h.left) y ((LPow A L a T).U j) (s.f j) :=
    fun j hj => (gs_res _ y _ hj _).trans (gs_pull _ h.left y _ (hl j hj) _)
  refine ((gs_res (𝟙 _) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y j j' hy.1 hy.2))) ((gs_res (𝟙 _) y _ hy _).trans (v j' hy.2)))).symm)
  refine (sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (𝟙 _ ≫ h.left) y
    (hl j hy.1) (hl j' hy.2)).trans ?_
  simp only [trF, Category.assoc, hc]
  try rfl

theorem exists_value (hL : L.IsLB) (a : ℤ) {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))) (hτ : τ.IsGen) :
    ∃ v, IsValueAt A L a s z τ v := by
  have hpz : (ptSecT A z).left ≫ (snd T A).left = z.left := by
    rw [← Over.comp_left]
    simp [ptSecT]
  obtain ⟨w, hw⟩ : ∃ w : ∀ j : Fin 1 → L.ι, Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j),
      ∀ j, w j = (T.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j)) *
        (show Γ(T.left, LB.wchart L (fun _ : Fin 1 => z.left) j) from ((τ.s j)⁻¹).val) := ⟨_, fun _ => rfl⟩
  have loc : ∀ j x, x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      gs (𝟙 _) x _ (w j) = gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) * ((gm (𝟙 _) x _ (τ.s j))⁻¹).val := by
    intro j x hx
    rw [hw j]
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) x (val_le A L z j) hx _).trans
      (gs_pull (𝟙 _) (ptSecT A z).left x _ (val_le A L z j hx) _)) ?_)
    exact (gs_unit (𝟙 _) x _ hx ((τ.s j)⁻¹)).trans (congrArg Units.val (map_inv _ _))
  have hcompat : TopCat.Presheaf.IsCompatible T.left.sheaf.obj (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) w := by
    intro j j'
    apply fn_ext
    intro x hx
    change gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_left).op).hom (w j)) =
      gs (𝟙 _) x _ ((T.left.presheaf.map (homOfLE inf_le_right).op).hom (w j'))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, loc j x hx.1, loc j' x hx.2]
    rw [show gs (𝟙 _ ≫ (ptSecT A z).left) x ((LPow A L a T).U j) (s.f j) = _ from
      sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s _ x
        (val_le A L z j hx.1) (val_le A L z j' hx.2)]
    rw [show gm (𝟙 _) x ((LB.LinComb L (fun _ : Fin 1 => z.left) fun _ => a).U j) (τ.s j) = _ from
      gen_trans hτ (𝟙 _) x hx.1 hx.2]
    have ht : trF (L := L) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _ ≫ (ptSecT A z).left) x j j' =
        trF (L := L) (fun _ : Fin 1 => z.left) (fun _ => a) (𝟙 _) x j j' := by
      simp only [trF, Category.assoc, hpz]
    rw [ht, mul_inv_rev, Units.val_mul]
    have key : ∀ (t G : (T.left.presheaf.stalk x)ˣ) (P : T.left.presheaf.stalk x),
        (t : T.left.presheaf.stalk x) * P * (((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) *
          ((t⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) =
          P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x) := by
      intro t G P
      linear_combination (P * ((G⁻¹ : (T.left.presheaf.stalk x)ˣ) : T.left.presheaf.stalk x)) * Units.mul_inv t
    exact key _ _ _
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => z.left) j := by
    intro x _
    have hx : z.left x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨v, hv, -⟩ := TopCat.Sheaf.existsUnique_gluing' T.left.sheaf
    (fun j : Fin 1 → L.ι => LB.wchart L (fun _ : Fin 1 => z.left) j) ⊤ (fun j => homOfLE le_top) hcov w hcompat
  refine ⟨v, fun j => ?_⟩
  have e : (T.left.presheaf.map (homOfLE le_top).op).hom v = w j := hv j
  have key : ∀ (R : Type) [CommRing R] (p : R) (t : Rˣ), p = p * ((t⁻¹ : Rˣ) : R) * (t : R) := by
    intro R _ p t
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [e, hw j]
  exact key _ _ (τ.s j)

theorem value_stalk (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by
  have h1 := congrArg (gs r y (LB.wchart L (fun _ : Fin 1 => z.left) j)) (hv j)
  refine ((gs_pull r (ptSecT A z).left y _ (val_le A L z j hy) _).symm.trans
    ((gs_res r y (val_le A L z j) hy _).symm.trans h1)).trans ?_
  exact (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y le_top hy v) (gs_unit r y _ hy _))

theorem pullSec_stalk (a : ℤ) {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a h hh s s') {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (y : Z) (j : Fin 1 → L.ι) (hy : r y ∈ (LPow A L a T').U j) :
    gs r y _ (s'.f j) = gs (r ≫ h.left) y _ (s.f j) := by
  rw [hs j]
  exact (gs_res r y (chart_le_res A L h hh a j) hy _).trans (gs_pull r h.left y _ (chart_le_res A L h hh a j hy) _)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvC
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

section Col

variable {S : Type} [CommRing S] {n d : ℕ}

def sb (b : Fin n) : Fin 1 × Fin d → MvPowerSeries (Fin n × Fin d) S := fun p => MvPowerSeries.X ((b, p.2))

theorem sb_cc (b : Fin n) (p : Fin 1 × Fin d) : MvPowerSeries.constantCoeff (sb (S := S) b p) = 0 := by
  first
  | simp [sb]
  | exact MvPowerSeries.constantCoeff_X _

theorem rename_col (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) F = MvPowerSeries.subst (sb b) F := by
  first
  | exact MvPowerSeries.rename_eq_subst _ _
  | exact (MvPowerSeries.subst_X_comp_eq_rename _ _).symm
  | (rw [MvPowerSeries.rename_eq_subst]; rfl)
  | (rw [← MvPowerSeries.subst_eq_rename]; rfl)
  | (rw [MvPowerSeries.subst_eq_rename]; rfl)

theorem subst_quadCol (b : Fin n) (r : S) (β : Matrix (Fin d) (Fin d) S) :
    MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) =
      r • ∑ i : Fin d, ∑ j : Fin d, MvPowerSeries.C (β i j) * MvPowerSeries.X (b, i) * MvPowerSeries.X (b, j) := by
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (sb (S := S) (n := n) (d := d) b p) = 0 := fun p => sb_cc b p
  have hs : MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := d) b) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hC : ∀ (c : S) (f : MvPowerSeries (Fin 1 × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  have hC' : ∀ (c : S) (f : MvPowerSeries (Fin n × Fin d) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  rw [← MvPowerSeries.coe_substAlgHom hs]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Fin.sum_univ_one, mul_assoc, hC, hC', map_smul, map_sum, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs, sb]

theorem sum_subst_quadCol (r : S) (β : Matrix (Fin d) (Fin d) S) :
    ∑ b : Fin n, MvPowerSeries.subst (sb b) (r • TB.quadCol (n := 1) β) = r • TB.quadCol (n := n) β := by
  simp only [subst_quadCol]
  simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Finset.smul_sum]

theorem cc_quadCol {m : ℕ} (β : Matrix (Fin d) (Fin d) S) :
    MvPowerSeries.constantCoeff (TB.quadCol (n := m) β) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.TB.quadCol]

end Col

theorem colIdx_degree {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (m : LtN Dw n →₀ ℕ) : (colIdx m).degree = m.degree := by
  classical
  have key : ∀ {α : Type} (e : α →₀ ℕ), e.degree = e.sum (fun _ k => k) := fun e => rfl
  rw [colIdx, key, key, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

private theorem hasSubst_lemma {S σ τ : Type} [CommRing S] [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

private theorem prod_exp_lemma_2 {S σ ι : Type} [CommRing S] [Algebra ℚ S] (s : Finset ι)
    (x : ι → MvPowerSeries σ S) (hx : ∀ i, MvPowerSeries.constantCoeff (x i) = 0) :
    ∏ i ∈ s, PowerSeries.subst (x i) (PowerSeries.exp S) = PowerSeries.subst (∑ i ∈ s, x i) (PowerSeries.exp S) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  · intro a s ha ih
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hx a)
      (by rw [map_sum]; exact Finset.sum_eq_zero (fun i _ => hx i))]

theorem harm_kill_jet {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n D : ℕ)
    (g g' : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (hj : ∀ b, psJet D (g' b) =
      psJet D (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)))
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (hD : ∀ m ∈ P.support, m.degree ≤ D) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
  classical

  have hccQ : ∀ (r : S) {m' : ℕ}, MvPowerSeries.constantCoeff (r • TB.quadCol (n := m') β) = 0 := by
    intro r m'
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cc_quadCol, mul_zero]
  have hsb : ∀ b : Fin n, MvPowerSeries.HasSubst (sb (S := S) (n := n) (d := dL Dw) b) :=
    fun b => hasSubst_lemma (sb_cc b)
  have hR : ∀ (b : Fin n) (F : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
      MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) F =
        MvPowerSeries.subst (sb b) F := fun b F => rename_col b F

  have hE4 : ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
        ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b) := by
    simp only [hR]
    simp only [MvPowerSeries.subst_mul (hsb _), Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    have hc : ∀ b : Fin n, MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b)
        (PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S)) =
        PowerSeries.subst (MvPowerSeries.subst (sb (S := S) (n := n) (d := dL Dw) b) ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β))
          (PowerSeries.exp S) := by
      intro b
      have hq : MvPowerSeries.HasSubst (fun _ : Unit => ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β)) :=
        hasSubst_lemma (fun _ => hccQ _)
      exact MvPowerSeries.subst_comp_subst_apply hq (hsb b) (PowerSeries.exp S)
    simp only [hc]
    rw [prod_exp_lemma_2 Finset.univ _ (fun b => ?_), sum_subst_quadCol]
    rw [subst_quadCol]
    simp [MvPowerSeries.smul_eq_C_mul]

  have hE2 : psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g' b)) =
      psJet D (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
        (g b * PowerSeries.subst ((k : S) • ReciprocityTheory.ChartRestriction.G.TB.quadCol (n := 1) β) (PowerSeries.exp S))) := by
    refine Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr D (fun b => ?_)
    rw [hR, hR]
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_subst_congr D (sb b) (sb_cc b) (hj b)

  have hK := Formalism.MainNotions.ModuliIntegralCharts.H1.killAddValCol_of ReciprocityTheory.ChartRestriction.G.TB.kernel_additive E H Dw l c S k n
    (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b))
    β (Formalism.MainNotions.ModuliIntegralCharts.H1.psiCover_holds H) hβ a P hP
  have hcan : PowerSeries.subst (-((k : S)) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
      PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) = 1 := by
    rw [← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (hccQ _) (hccQ _), neg_smul, neg_add_cancel,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.expS, ← mul_assoc, hcan, one_mul] at hK
  calc ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g' b) (colOf m b)
      = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (PowerSeries.subst ((k : S) • TB.quadCol (n := n) β) (PowerSeries.exp S) *
            ∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [← Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g' m, ← hE4]
        congr 1
        unfold Formalism.MainNotions.ModuliIntegralCharts.H1.mVal
        rw [Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.coeff_eq_of_psJet hE2 (by rw [colIdx_degree]; exact hD m hm)]
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m :=
        hK.symm
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) :=
        Finset.sum_congr rfl (fun m _ => by rw [Formalism.MainNotions.ModuliIntegralCharts.H1.prodCol_holds E H Dw S n g m])

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LBPull
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section GenX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end GenX

section Sec

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isPullSec_congr {T T' : Over S0} {h₁ h₂ : T' ⊗ A ⟶ T ⊗ A} (e : h₁ = h₂)
    (hh₁ : h₁ ≫ snd T A = snd T' A) (hh₂ : h₂ ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a h₁ hh₁ s s' ↔ IsPullSec A L a h₂ hh₂ s s' := by
  subst e
  exact Iff.rfl

theorem isPullSec_unique {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' s'' : LB.Sec (LPow A L a T')}
    (h' : IsPullSec A L a h hh s s') (h'' : IsPullSec A L a h hh s s'') : s' = s'' := by
  obtain ⟨f1, c1⟩ := s'
  obtain ⟨f2, c2⟩ := s''
  have hf : f1 = f2 := funext fun j => (h' j).trans (h'' j).symm
  subst hf
  rfl

end Sec

section Val

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem ptSecT_whisker {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (g ≫ z)).left ≫ (g ▷ A).left = g.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (g ≫ z) ≫ (g ▷ A) = g ≫ ptSecT A z := by
    unfold ptSecT
    ext <;> simp
  have e' := congrArg CommaMorphism.left e
  simpa using e'

theorem isValueAt_pull {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) :
    IsValueAt A L a s' (g ≫ z) (LB.pullGen L (fun _ => z.left) (fun _ => a) τ g.left) (g.left.appTop.hom v) := by
  intro j
  have hW : ∀ x ∈ LB.wchart L (fun _ : Fin 1 => (g ≫ z).left) j,
      g.left x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j := fun x hx =>
    Set.mem_iInter.2 fun k => by
      have h1 := Set.mem_iInter.1 hx k
      simpa [Over.comp_left, Scheme.Hom.comp_base] using h1
  apply fn_ext
  intro x hx
  have hx' := hW x hx
  have hPz := val_le A L z j hx'
  have hPgz := val_le A L (g ≫ z) j hx

  erw [gs_res _ x _ hx, gs_pull (𝟙 _) _ x _ hPgz, Category.id_comp, hs j,
    gs_res _ x _ hPgz, gs_pull (ptSecT A (g ≫ z)).left (g ▷ A).left x ((LPow A L a T).U j)
      (chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j
        (show (ptSecT A (g ≫ z)).left x ∈ (LPow A L a T').U j from hPgz)),
    ptSecT_whisker, ← gs_pull g.left (ptSecT A z).left x _ hPz, ← gs_res _ x (val_le A L z j) hx',
    hv j, gs_mul _ x _ hx', gs_res _ x le_top hx']

  erw [gs_mul _ x _ hx, gs_res _ x le_top hx, gs_pull (𝟙 T'.left) g.left x ⊤ (by simp), Category.id_comp]
  congr 1
  dsimp only
  show gs g.left x (LB.wchart L (fun _ : Fin 1 => z.left) j) (τ.s j).val =
    gs (𝟙 _) x _ (((T'.left.presheaf.map (homOfLE _).op).hom ((g.left.app _).hom (τ.s j).val)))
  erw [gs_res _ x _ hx, gs_pull (𝟙 _) g.left x _ hx', Category.id_comp]

end Val

section Rig

private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem shape_rig {X T T' : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X) (hf : g ≫ f = f')
    {U : X.Opens} {W : T.Opens} (hW : W ≤ f ⁻¹ᵁ U) {V : T'.Opens} (hV : V ≤ g ⁻¹ᵁ W) {V' : T'.Opens}
    (hV' : V' ≤ f' ⁻¹ᵁ U) {O : T'.Opens} (o1 : O ≤ V) (o2 : O ≤ V') (x : Γ(X, U)ˣ) (k : ℤ) :
    res o1 (res hV (pullU g W ((res hW (pullU f U x)) ^ k))) = res o2 ((res hV' (pullU f' U x)) ^ k) := by
  subst hf
  have hA : V ≤ (g ≫ f) ⁻¹ᵁ U := fun y hy => hW (hV hy)
  simp only [map_zpow]
  congr 1
  rw [← DVR.res_pullU_comp' g f hW hV hA x, res_res_lemma, res_res_lemma]

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

theorem corr_rigT_pull (rig : LB.Gen (L.pull (eSec A))) {T T' : Over S0} (g : T' ⟶ T) (k : ℤ) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (rigT A L rig T k) g.left) (rigT A L rig T' k) := by
  unfold LB.Gen.Corr
  intro j j' _ _ hjj
  have hj : j = j' := funext fun i => by
    fin_cases i
    exact hjj 0 0 (by rw [← Category.assoc, Over.w g])
  subst hj
  exact shape_rig g.left T.hom T'.hom (Over.w g) _ _ _ _ _ _ k

end Rig

section SecComp

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isPullSec_comp {T T' T'' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {h' : T'' ⊗ A ⟶ T' ⊗ A} {hh' : h' ≫ snd T' A = snd T'' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} {s'' : LB.Sec (LPow A L a T'')}
    (h1 : IsPullSec A L a h hh s s') (h2 : IsPullSec A L a h' hh' s' s'') :
    IsPullSec A L a (h' ≫ h) (by rw [Category.assoc, hh, hh']) s s'' := by
  intro j
  rw [h2 j, h1 j]
  simp only [Over.comp_left, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE_assoc]

end SecComp

end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
end
end

