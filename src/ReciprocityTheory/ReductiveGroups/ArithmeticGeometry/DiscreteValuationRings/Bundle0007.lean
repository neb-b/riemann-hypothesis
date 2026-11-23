module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing

section Gen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem gs_sum (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq f z U h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (gs_eq f z U h (a i)).symm

theorem secScal_sval {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = sval s₁ r z J := by
  have hj : ∀ k, (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) : K₁ ⊕ K₂ → L.ι) k =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) k) := by
    intro k; cases k <;> rfl
  have hcoh : LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := fun k₁ k₂ hk => by
    rw [hj, hj, hk]
  have H' := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) hcoh
  have hm1 : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) :=
    show r.base z ∈ (⋂ k, ((φ₁ k).base ⁻¹' (L.U (J (r ≫ φ₁ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ φ₁ k)
  have hm2 : r z ∈ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    show r.base z ∈ (⋂ k, ((h ≫ φ₂ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ₂ k)) : Set X))) from
      Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ₂ k)
  have hm : r z ∈ (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) := ⟨hm1, hm2⟩
  have hle2 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) := inf_le_right.trans (wchart_comp_le φ₂ h (fun k => J (r ≫ h ≫ φ₂ k)))
  have hle1 : (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ≤ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) := inf_le_left
  have l1 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) ((Y'.presheaf.map (homOfLE hle2).op).hom ((h.app _).hom (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))))) =
      gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k))) (s₂.f (fun k => J (r ≫ h ≫ φ₂ k))) :=
    (gs_res r z hle2 hm _).trans (gs_pull r h z _ (hle2 hm) _)
  have l2 : gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) (resTop (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k))) 1 * (Y'.presheaf.map (homOfLE hle1).op).hom (s₁.f (fun k => J (r ≫ φ₁ k)))) =
      gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k))) := by
    simp only [resTop, map_one]
    rw [_root_.one_mul]
    exact gs_res r z hle1 hm _
  have key := congrArg (gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)))) H'
  have e : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ h ≫ φ₂ k)) := by
    funext k; rw [Category.assoc]
  show gs (r ≫ h) z (LB.wchart L φ₂ (fun k => J ((r ≫ h) ≫ φ₂ k)))
      (s₂.f (fun k => J ((r ≫ h) ≫ φ₂ k))) = gs r z (LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k))) (s₁.f (fun k => J (r ≫ φ₁ k)))
  rw [e]
  exact l1.symm.trans (key.trans l2)

theorem secScal_of_sval (hL : L.IsLB) {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J → sval s₂ (𝟙 Y' ≫ h) y J = sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1 := by
  intro j₁ j₂ hc
  simp only [resTop, map_one, _root_.one_mul]
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
  have := H y J hJ
  rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
    sval_of s₂ _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
  have le : LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact ((gs_res _ y _ hy _).trans (gs_pull _ h y _ (le hy.2) _)).trans (this.trans (gs_res _ y _ hy _).symm)

theorem sval_lin {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ j : K → L.ι, s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (b i) * sval (t i) r z J := by
  have hmem : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((φ k).base ⁻¹' (L.U (J (r ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  show gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k))) = _
  rw [hs, gs_sum r z _ hmem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hmem]
  congr 1
  exact gs_res r z le_top hmem (b i)

theorem sval_pullSec {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  have hmem : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) := by
    show r.base z ∈ (⋂ k, ((h ≫ φ k).base ⁻¹' (L.U (J (r ≫ h ≫ φ k)) : Set X)))
    exact Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  calc sval (pullSec L φ ε s h) r z J
      = gs r z (LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)))
          ((Y'.presheaf.map (homOfLE (wchart_comp_le φ h (fun k => J (r ≫ h ≫ φ k)))).op).hom
            ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k))))) := rfl
    _ = gs r z (h ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
          ((h.app _).hom (s.f (fun k => J (r ≫ h ≫ φ k)))) :=
        gs_res r z (wchart_comp_le φ h _) hmem _
    _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k))) (s.f (fun k => J (r ≫ h ≫ φ k))) :=
        gs_pull r h z _ (wchart_comp_le φ h _ hmem) _
    _ = sval s (r ≫ h) z J := by
        have e : (fun k => J ((r ≫ h) ≫ φ k)) = fun k => J (r ≫ h ≫ φ k) := by
          funext k; rw [Category.assoc]
        show _ = gs (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)))
          (s.f (fun k => J ((r ≫ h) ≫ φ k)))
        rw [e]

end Gen

section Move

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem gs_gF_comp {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hf : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    (y : (DegPre.BF D.toPre F).left) (ζ : F) :
    gs h y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  calc gs h y ⊤ (gF D.toPre F ζ)
      = gs (h ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
        gs_pull h (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _
    _ = gs (𝟙 _ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by rw [hf, Category.id_comp]
    _ = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) :=
        (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp) _).symm

theorem vge_move {k : ℕ} {α χ : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    {s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))}
    {h : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left}
    (hfst : h ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left)
    {TB : D.toPre.P.A.left ⟶ D.toPre.P.A.left}
    (hh : h ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ TB)
    {K₃ K₄ : Type} [Fintype K₃] [Fintype K₄]
    {φ₃ : K₃ → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb D.toPre.P.L φ₃ ε₃))
    (hrel : GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s'
      (DegPre.famφ D.toPre F α) (DegPre.famε k) s h φ₃ ε₃ u)
    {ψ : K₄ → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {δ : K₄ → ℤ}
    (eB : LB.Gen (LB.LinComb D.toPre.P.L ψ δ)) (heB : eB.IsGen)
    (hform : FormEq (Sum.elim (fun i => TB ≫ D.toPre.famφB α i) ψ) (Sum.elim (DegPre.famε k) δ)
      (D.toPre.famφB χ) (DegPre.famε k))
    (c : F)
    (hc : ∀ (y : (DegPre.BF D.toPre F).left) (J : ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L y J →
      (val u (𝟙 _) y J).val = gs (𝟙 _) y ⊤ (gF D.toPre F c) * (val eB (DegPre.prB D.toPre F).left y J).val)
    {r q : ℚ} (hq : ((q : ℚ) : WithTop ℚ) ≤ v c) (hs : VGe D F v k α s r) : VGe D F v k χ s' (r + q) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  have e1 : ∀ i, ∃ t : D.toPre.SecB k χ, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval t ρ z J = sval (σ i) (ρ ≫ TB) z J * (val eB ρ z J).val := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hform (pullMulSec (σ i) TB eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ heB ρ z hJ)⟩
  choose σ' hσ' using e1
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  have e2 : ∀ i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (σ' i) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun i => by
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (σ' i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose σ'F hσ'F using e2
  refine ⟨n, fun i => c * a i, σ', σ'F, fun i => ?_, fun i => ?_, fun j => ?_⟩
  · exact secScal_of_sval hL fun y J hJ => (hσ'F i _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm ((r : ℚ) : WithTop ℚ)]
    exact add_le_add hq (hva i)
  · show s'.f j = ∑ i, resTop _ (gF D.toPre F (c * a i)) * (σ'F i).f j
    refine fn_ext fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left =>
      Geo.Tor.exists_chart hL (ψ y)
    have hIy : Good D.toPre.P.L y I := hI
    have m := hIy.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    have hy' : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j := hy
    have T0 := sec_trans s' (𝟙 _) y hy' m
    set τ := (Geo.Tor.trF (DegPre.famφ D.toPre F χ) (DegPre.famε k) (𝟙 _) y j
      (fun k => I (𝟙 _ ≫ DegPre.famφ D.toPre F χ k))).val with hτ
    have Ti : ∀ i, gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * (gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I) := fun i => by
      have S1 : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
          (resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i))) =
          gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) := gs_res _ y le_top hy' _
      rw [gs_mul _ y _ hy', S1, sec_trans (σ'F i) (𝟙 _) y hy' m, hτ]
      exact mul_left_comm _ _ _
    have RHS : gs (𝟙 _) y (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j)
        (∑ i, resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (gF D.toPre F (c * a i)) *
          (show Γ((DegPre.BF D.toPre F).left, LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) from (σ'F i).f j)) =
        τ * ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      rw [gs_sum _ y _ hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Ti i
    have CORE : sval s' (𝟙 _) y I = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c * a i)) * sval (σ'F i) (𝟙 _) y I := by
      have H1 := (secRel_iff hL _ _ s' _ _ s h _ _ u).1 hrel _ (𝟙 _) y I hIy
      have H2 := sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) (𝟙 _ ≫ h) y hIy
      rw [H1, H2, hc y I hIy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have A1 : gs (𝟙 _ ≫ h) y ⊤ (gF D.toPre F (a i)) = gs (𝟙 _) y ⊤ (gF D.toPre F (a i)) := by
        rw [Category.id_comp]; exact gs_gF_comp hfst y (a i)
      have A2 : sval (σF i) (𝟙 _ ≫ h) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I := by
        rw [← secScal_sval (hscal i) (𝟙 _ ≫ h) y hIy, Category.assoc, hh, Category.id_comp]
      have A3 : sval (σ'F i) (𝟙 _) y I = sval (σ i) ((DegPre.prB D.toPre F).left ≫ TB) y I *
          (val eB (DegPre.prB D.toPre F).left y I).val := by
        rw [hσ'F i _ (𝟙 _) y I hIy, Category.id_comp, hσ' i _ _ y I hIy]
      rw [A1, A2, A3, map_mul, gs_mul _ y ⊤ (by trivial)]
      ring
    exact T0.trans ((congrArg (fun x => τ * x) CORE).trans RHS.symm)

end Move

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThickKer
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] {X : Scheme.{0}}

def strMap (p : X ⟶ Sp V) (U : X.Opens) : V →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom

theorem constFn_eq_strMap (p : X ⟶ Sp V) (U : X.Opens) (a : V) : constFn p U a = strMap p U a := rfl

theorem fromSpec_appLE_top {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem appLE_top_eq {Y W : Scheme.{0}} (f : Y ⟶ W) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)

theorem mem_map_of_app_fst_eq_zero (p : X ⟶ Sp V) (J : Ideal V) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U))
    (ha : ((pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom a = 0) :
    a ∈ J.map (strMap p U) := by
  let I₀ : Ideal Γ(X, U) := J.map (strMap p U)
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I₀ := Ideal.Quotient.mk I₀
  let ψ : V ⧸ J →+* Γ(X, U) ⧸ I₀ := Ideal.quotientMap I₀ (strMap p U) Ideal.le_comap_map
  let z : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  have hz : ⊤ ≤ z ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : z.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : z.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp, fromSpec_appLE_top]
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (z.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  have m1 : (z ≫ p).appTop = p.appLE ⊤ U le_top ≫ z.appLE U ⊤ hz :=
    ((Scheme.Hom.appLE_comp_appLE z p ⊤ U ⊤ le_top hz).trans (appLE_top_eq _ _)).symm
  have m5 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))).symm
  have m6 : (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop =
      CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)).symm
  have e5 : ∀ c : V, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J c) :=
    fun c => congrArg (fun φ => φ.hom c) m5
  have e6 : ∀ c : V ⧸ J, (Spec.map (CommRingCat.ofHom ψ)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).inv.hom (ψ c) :=
    fun c => congrArg (fun φ => φ.hom c) m6
  have hsq : z ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1
    ext b
    show (z ≫ p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b) =
      (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)
    rw [m1, Scheme.Hom.comp_appTop]
    show (z.appLE U ⊤ hz).hom ((p.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b)) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b))
    rw [k1, e5, e6, Ideal.quotientMap_mk]
    rfl
  let l := pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) hsq
  have hl : l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) = z := pullback.lift_fst _ _ _
  have tr : ∀ (w : Spec (CommRingCat.of (Γ(X, U) ⧸ I₀)) ⟶ X) (hw : w = z) (e : ⊤ ≤ w ⁻¹ᵁ U),
      (w.appLE U ⊤ e).hom a = (z.appLE U ⊤ hz).hom a := by
    intro w hw e
    subst hw
    rfl
  have k2 : ((l ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appLE U ⊤
      (hl ▸ hz)).hom a = 0 := by
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  rw [tr _ hl, k1] at k2
  have h1 : q a = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I₀))).hom.hom k2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem loc_div {P : Scheme.{0}} (p' : P ⟶ Sp V) (W : P.Opens) (f : Γ(P, W)) (r : V) (x : P) (hx : x ∈ W)
    (h : cst p' x r ∣ gs (𝟙 P) x W f) : ∃ (U : P.Opens) (_ : U ≤ W) (_ : x ∈ U) (g : Γ(P, U)),
      ∀ y ∈ U, gs (𝟙 P) y W f = cst p' y r * gs (𝟙 P) y U g := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨U, hU, g, rfl⟩ := P.presheaf.exists_germ_eq t
  have hm : x ∈ W ⊓ U := ⟨hx, hU⟩
  have e : gs (𝟙 P) x (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) x (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := by
    rw [gs_res _ x _ hm, gs_mul _ x _ hm, gs_res _ x _ hm, gs_constFn p' _ _ x hm, Category.id_comp, ht,
      gs_eq _ x U hU]
    rfl
  rw [gs_eq _ x _ hm, gs_eq _ x _ hm] at e
  obtain ⟨U', hU', i₁, i₂, e'⟩ := P.presheaf.germ_eq x hm hm _ _ e
  have le : U' ≤ W ⊓ U := i₁.le
  refine ⟨U', le.trans inf_le_left, hU', (P.presheaf.map (homOfLE (le.trans inf_le_right)).op).hom g, fun y hy => ?_⟩
  have e'' := congrArg (gs (𝟙 P) y U') e'
  have k := (gs_res (𝟙 P) y le hy _).symm.trans (e''.trans (gs_res (𝟙 P) y le hy _))
  have hy' : (𝟙 P : P ⟶ P) y ∈ W ⊓ U := le hy
  have k' : gs (𝟙 P) y (W ⊓ U) ((P.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs (𝟙 P) y (W ⊓ U) (constFn p' (W ⊓ U) r * (P.presheaf.map (homOfLE inf_le_right).op).hom g) := k
  rw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_constFn p' _ _ y hy', Category.id_comp] at k'
  rw [k', gs_res _ y _ hy]

theorem dvd_germ_of_thick (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) {W : X.Opens}
    (a : Γ(X, W)) (x' : ↑(pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hx : pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' ∈ W)
    (h : cst (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫ p) x' r ∣
      gs (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) x' W a) :
    cst p (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') r ∣
      gs (𝟙 X) (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x') W a := by
  let P := pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  let f : P ⟶ X := pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of V) J
  have : IsClosedImmersion f := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have h' : cst (f ≫ p) x' r ∣ gs (𝟙 P) x' (f ⁻¹ᵁ W) ((f.app W).hom a) := by
    rw [gs_pull (𝟙 P) f x' W hx, Category.id_comp]; exact h
  obtain ⟨U', hU'W, hxU', t', ht'⟩ := loc_div (f ≫ p) (f ⁻¹ᵁ W) ((f.app W).hom a) r x' hx h'
  obtain ⟨O, hO, hOeq⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.1 U'.isOpen
  have hxO : f x' ∈ O := by
    have : x' ∈ f.base ⁻¹' O := by rw [hOeq]; exact hxU'
    exact this
  obtain ⟨U, hU, hxU, hUsub⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
    (show f x' ∈ (⟨O, hO⟩ ⊓ W : X.Opens) from ⟨hxO, hx⟩)
  have hUW : U ≤ W := hUsub.trans inf_le_right
  have hfU : f ⁻¹ᵁ U ≤ U' := fun y hy => by
    have hyO : f y ∈ O := (hUsub hy).1
    have : y ∈ f.base ⁻¹' O := hyO
    rw [hOeq] at this
    exact this
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective f U hU ((P.presheaf.map (homOfLE hfU).op).hom t')
  have hd : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a) = (f.app U).hom (constFn p U r * b) := by
    apply fn_ext
    intro y hy
    have hyW : f y ∈ W := hUW hy
    have L1 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy ((X.presheaf.map (homOfLE hUW).op).hom a)
      rw [Category.id_comp, gs_res f y hUW hy] at e1
      have e2 := gs_pull (𝟙 P) f y W hyW a
      rw [Category.id_comp] at e2
      rw [e1, ← e2]
      exact ht' y (hfU hy)
    have L2 : gs (𝟙 P) y (f ⁻¹ᵁ U) ((f.app U).hom (constFn p U r * b)) =
        cst (f ≫ p) y r * gs (𝟙 P) y U' t' := by
      have e1 := gs_pull (𝟙 P) f y U hy (constFn p U r * b)
      rw [Category.id_comp, gs_mul f y U hy, gs_constFn p U f y hy] at e1
      have e3 := gs_pull (𝟙 P) f y U hy b
      rw [Category.id_comp, hb, gs_res (𝟙 P) y hfU hy] at e3
      rw [e1, e3]
    exact L1.trans L2.symm
  have hd0 : (f.app U).hom ((X.presheaf.map (homOfLE hUW).op).hom a - constFn p U r * b) = 0 := by
    rw [map_sub, hd, sub_self]
  have hmem := mem_map_of_app_fst_eq_zero p J hU _ hd0
  have hle : J.map (strMap p U) ≤ Ideal.span {strMap p U r} := by
    refine (Ideal.map_mono hJ).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hle hmem)
  have ha : (X.presheaf.map (homOfLE hUW).op).hom a = constFn p U r * (b + c) := by
    rw [mul_add, ← constFn_eq_strMap] at *
    linear_combination -hc
  refine ⟨gs (𝟙 X) (f x') U (b + c), ?_⟩
  rw [← gs_res (𝟙 X) (f x') hUW hxU, ha, gs_mul (𝟙 X) (f x') U hxU, gs_constFn p U (𝟙 X) (f x') hxU, Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

