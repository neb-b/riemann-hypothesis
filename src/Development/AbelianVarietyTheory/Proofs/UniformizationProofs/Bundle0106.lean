module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSuccOfRelAmple
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open LBGerm

theorem IsAmpleLB.exists_sec_succ {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (x : X) :
    ∃ n, 1 ≤ n ∧ ∃ (a : (lbPow L n).Sec) (b : (lbPow L (n + 1)).Sec), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨n, hn, s, hs, hr, -⟩ := h.exists_affine_le hi
  have le : ∀ J : PUnit → L.ι, nonzeroLocus s ⊓ powChart L J ≤ L.U (J PUnit.unit) ⊓ L.U i :=
    fun J y hy => ⟨mem_powChart.1 hy.2, hr hy.1⟩
  have hg : ∀ (J : PUnit → L.ι) (y : X), y ∈ nonzeroLocus s ⊓ powChart L J →
      gs (𝟙 X) y _ (resG X (le J) (L.g (J PUnit.unit) i).val) =
        (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U i) (L.g (J PUnit.unit) i)).val := fun J y hy =>
    (gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y _ (le J hy) _)
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 1) hL s (fun J => resG X (le J) (L.g (J PUnit.unit) i).val)
    (mem_secOn_of_germ (M := lbPow L 1) _ fun y J J' h hJ hJ' => by
      rw [gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ', pow_one]
      refine (hg J y ⟨h, hJ⟩).trans (Eq.trans ?_ (congrArg _ (hg J' y ⟨h, hJ'⟩)).symm)
      rw [← Units.val_mul, gm_cocycle hL (𝟙 X) y (mem_powChart.1 hJ) (mem_powChart.1 hJ') (hr h)])
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  refine ⟨n * (N + 1), Nat.mul_pos hn (Nat.succ_pos N), secPow s (N + 1), secCast (Nat.add_comm _ _) u, ?_, ?_⟩
  · rwa [nonzeroLocus_secPow s (Nat.succ_pos N)]
  · have hJ : x ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have hy : x ∈ nonzeroLocus s ⊓ powChart L (fun _ => i) := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, hg _ x hy] at e
    rw [nonzeroLocus_secCast, mem_nonzeroLocus_iff_powFn u hJ, e]
    exact (((mem_nonzeroLocus_iff_powFn s hJ).1 hs).pow _).mul (Units.isUnit _)

theorem exists_sec_succ_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ x : X.left, ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L n) (b : H0 L (n + 1)), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  intro R _ X _ L hL hA x
  obtain ⟨n, hn, a, b, ha, hb⟩ := (isAmpleLB_of_relAmple_of_isAffine X hL hA).exists_sec_succ x
  obtain ⟨a', ha', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n : ℕ) : ℤ)) rfl a
  obtain ⟨b', hb', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n + 1 : ℕ) : ℤ)) rfl b
  exact ⟨n, hn, a', b', ha'.ge ha, hb'.ge hb⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecTwist
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PullPair

open LBGerm GlobalTheory.AbLaw

def chartPullTw {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t) (𝟙 X) where
  idx J := (fun _ => J 0, fun _ => J 1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1⟩
  g y J J' hJ hJ' := by
    have a₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 1
    have b₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J' 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 1
    refine (gm_linComb L _ _ (𝟙 X) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t y
      (fun _ => J 0, fun _ => J 1) (fun _ => J' 0, fun _ => J' 1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb L _ _ (𝟙 X) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp]

theorem exists_sec_twist {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (f : X ⟶ X) (e : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (y : X) : ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have hLB := h.isLB
  obtain ⟨n, hn, hc⟩ := h.exists_cover_mul
  obtain ⟨N, s, hs, ha⟩ := hc k hk
  have : CompactSpace X := h.compactSpace
  have : QuasiSeparatedSpace X := h.quasiSeparatedSpace
  obtain ⟨i, hi⟩ : ∃ i, y ∈ nonzeroLocus (s i) := by
    have hy : y ∈ (⨆ i, nonzeroLocus (s i)) := hs ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  have hM := LB.isLB_linComb hLB (fun _ : PUnit => f) (fun _ => e)
  have hH := isLB_lbPow hLB (n * k)
  obtain ⟨V, N', hyV, hV⟩ := GlobalTheory.TwistGen.exists_nhds hM hH (s i) (ha i) y hi
  obtain ⟨u, hu⟩ := hV 1
  have hmul : n * k * (N' + 1) = k * (n * (N' + 1)) := by ring
  refine ⟨n * (N' + 1), Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  rw [← hmul]
  refine ⟨chartSec (chartPullTw L f e (n * k) (N' + 1)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id]
  · exact hu hyV
  · intro z j hj
    refine ⟨![j.1 PUnit.unit, j.2 PUnit.unit], Set.mem_iInter.2 fun m => ?_⟩
    fin_cases m
    · exact Set.mem_iInter.1 hj.1 PUnit.unit
    · exact Set.mem_iInter.1 hj.2 PUnit.unit

theorem exists_cross : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A F j, ∃ t₁' t₂' : SecA A F (k * n), Cross a t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A.L z J → sA t₂ (ptSecT A.A 1).left z J ≠ 0) → (∀ z J, Good A.L z J → sA t₂' (ptSecT A.A 1).left z J ≠ 0)) := by
  intro _ R _ _ A F _ _ a ha j k hk
  have hamp : IsAmpleLB A.L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample
  have hUq : Unique (TFK (R := R) F).left := by
    unfold TFK
    exact inferInstanceAs (Unique (Spec (CommRingCat.of F)))
  obtain ⟨n, hn, u, hu⟩ := PullPair.exists_sec_twist hamp a.left (-(j : ℤ)) k hk
    ((1 : TFK (R := R) F ⟶ A.A).left default)
  have hασ : ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) A.A).left ≫ a.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have hF : FormEq (Sum.elim (fun m => (snd (TFK (R := R) F) A.A).left ≫ (![a.left, 𝟙 A.A.left] : Fin 2 → _) m)
      (fun _ : Fin 1 => ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left))
      (Sum.elim (![-(j : ℤ), ((k * n : ℕ) : ℤ)] : Fin 2 → ℤ) (fun _ : Fin 1 => (j : ℤ)))
      (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => ((k * n : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, hασ]
    rw [mul_right_comm, ← zpow_add, neg_add_cancel, zpow_zero, _root_.one_mul]
  refine ⟨n, hn, fun (t₁ t₂ : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (fun _ => (j : ℤ)))) => ?_⟩
  obtain ⟨s₁, hs₁⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₁ ((TFK (R := R) F) ◁ a).left))
  obtain ⟨s₂, hs₂⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₂ ((TFK (R := R) F) ◁ a).left))
  refine ⟨s₁, s₂, ?_, ?_⟩
  · intro z J hJ
    unfold sA
    rw [hs₁ _ _ z J hJ, hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
    simp only [Category.id_comp]
    ring
  · intro hne z J hJ
    have hr : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ ((TFK (R := R) F) ◁ a).left =
        (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_whiskerLeft, MonObj.one_comp]
    have hs : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
        (1 : TFK (R := R) F ⟶ A.A).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_snd]
    have hne' := hne z J hJ
    unfold sA at hne' ⊢
    rw [hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, hr]
    have hmem : ((ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left) z ∈
        nonzeroLocus u := by
      rw [hs, Subsingleton.elim z default]
      exact hu
    unfold nonzeroLocus at hmem
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hmem
    have hunit := ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval u _ z hJ i hi
    exact fun h0 => hne' ((hunit.mul_right_eq_zero).1 h0)

end GlobalTheory.PullPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtOfSecPullEq
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem ι_comp_eq_of_gs_eq {X Z : Scheme.{0}} (f g : Z ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (W : Z.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) (h : ∀ (a : Γ(X, U)), ∀ z ∈ W, gs f z U a = gs g z U a) :
    W.ι ≫ f = W.ι ≫ g := by
  have key : ∀ (U' : X.Opens) (hU' : U' = U) (V : Z.Opens) (hV : V ≤ W) (e₁ : V ≤ f ⁻¹ᵁ U') (e₂ : V ≤ g ⁻¹ᵁ U'),
      f.appLE U' V e₁ = g.appLE U' V e₂ := by
    intro U' hU' V hV e₁ e₂
    subst hU'
    ext a
    refine TopCat.Presheaf.section_ext Z.sheaf V _ _ fun z hz => ?_
    have hfz : f z ∈ U' := e₁ hz
    have hgz : g z ∈ U' := e₂ hz
    have := h a z (hV hz)
    rw [gs_eq f z U' hfz, gs_eq g z U' hgz] at this
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    erw [Z.presheaf.germ_res_apply, Z.presheaf.germ_res_apply]
    exact this
  rw [← f.resLE_comp_ι hf, ← g.resLE_comp_ι hg]
  congr 1
  have : IsAffine U := hU
  apply ext_of_isAffine
  show (Scheme.Hom.resLE f U W hf).app ⊤ = (Scheme.Hom.resLE g U W hg).app ⊤
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, Scheme.Hom.resLE_appLE]
  exact key _ (Scheme.Opens.ι_image_top U) _ (Scheme.Opens.ι_image_le _ _) _ _

private theorem hom_mul_eq_mul_of_eq_mul {R R' S : CommRingCat} (φ : R ⟶ S) (ψ : R' ⟶ S) (x y : R) (x' y' : R')
    (G₁ G₂ : S) (hx : φ.hom x = G₁ * ψ.hom x') (hy : φ.hom y = G₂ * ψ.hom y') :
    φ.hom (x * y) = (G₁ * G₂) * ψ.hom (x' * y') := by
  rw [map_mul, map_mul, hx, hy]
  ring

theorem exists_sec_extend_pos {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB)
    {N : ℕ} (s : H0 L N) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (N * m)), 1 ≤ m ∧ ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL N s).1 a
  refine ⟨m + 1, ⟨fun j => s.f j * @id Γ(X, (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U j) (t.f j), fun i j => ?_⟩, by omega, fun x i hx hi => ?_⟩
  · have hc : ((N * (m + 1) : ℕ) : ℤ) = (N : ℤ) + ((N * m : ℕ) : ℤ) := by push_cast; ring
    have key := hom_mul_eq_mul_of_eq_mul _ _ (s.f i) (t.f i) (s.f j) (t.f j) _ _ (s.compat i j) (t.compat i j)
    refine key.trans (congrArg₂ (· * ·) ?_ rfl)
    dsimp only [LB.LinComb]
    rw [Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_one, hc, zpow_add]
    exact (Units.val_mul _ _).symm
  · have hw : (𝟙 X) x ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hi
    have e := gs_mul (𝟙 X) x _ hw (s.f fun _ => i) (t.f fun _ => i)
    have ht' : gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (t.f fun _ => i) =
        gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (s.f fun _ => i) ^ m *
          gs (𝟙 X) x _ a := ht x (fun _ => i) hx hi
    refine e.trans ?_
    rw [ht']
    ring

private theorem gs_eq_stalkMap_gs_id_uniformization {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (hz : r z ∈ U) (b : Γ(X, U)) :
    gs r z U b = (r.stalkMap z).hom (gs (𝟙 X) (r z) U b) := by
  rw [gs_eq r z U hz, gs_eq (𝟙 X) (r z) U hz]
  have e := congrArg (fun φ => φ.hom b) (r.germ_stalkMap U z hz)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.symm

theorem gs_pull_extend {X Z : Scheme.{0}} {L : LB X} {N n m : ℕ} (s : H0 L N) (t : H0 L n) (a : Γ(X, nonzeroLocus s))
    (h : ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a)
    (r : Z ⟶ X) (z : Z) (i : L.ι) (hz : r z ∈ nonzeroLocus s) (hi : r z ∈ L.U i) :
    gs r z _ (t.f fun _ => i) = gs r z _ (s.f fun _ => i) ^ m * gs r z _ a := by
  have hw : r z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := (mem_wchart_oneTerm (0 : Fin 1)).2 hi
  have hwn : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => i) := hw
  have hwN : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) := hw
  rw [gs_eq_stalkMap_gs_id_uniformization r z _ hwn, gs_eq_stalkMap_gs_id_uniformization r z _ hwN, gs_eq_stalkMap_gs_id_uniformization r z _ hz, h (r z) i hz hi, map_mul, map_pow]

private theorem isUnit_gs_of_mem_basicOpen' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hb : r z ∈ X.basicOpen b) : IsUnit (gs r z U b) := by
  have hU : r z ∈ U := X.basicOpen_le b hb
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU]
  exact ((X.mem_basicOpen b (r z) hU).1 hb).map (r.stalkMap z).hom

private theorem mem_basicOpen_of_isUnit_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hU : r z ∈ U) (hb : IsUnit (gs r z U b)) : r z ∈ X.basicOpen b := by
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU] at hb
  rw [X.mem_basicOpen b (r z) hU]
  exact (isUnit_map_iff (r.stalkMap z).hom _).1 hb

private theorem exists_mem_basicOpen_of_mem_nonzeroLocus {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) {x : X}
    (hx : x ∈ nonzeroLocus a) : ∃ j : L.ι, x ∈ X.basicOpen (a.f fun _ => j) := by
  unfold nonzeroLocus at hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨j, rfl⟩ : ∃ j, k = fun _ => j := ⟨k 0, funext fun q => congrArg k (Subsingleton.elim q 0)⟩
  exact ⟨j, hk⟩

private theorem mem_nonzeroLocus_of_mem_basicOpen {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) (j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (a.f fun _ => j)) : x ∈ nonzeroLocus a := by
  unfold nonzeroLocus
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, hx⟩

private theorem exists_mem_chart' {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ j, x ∈ L.U j := by
  have hx : x ∈ ⨆ i, L.U i := by
    rw [hL.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

theorem hom_ext_of_sec_pull_eq : ∀ (X Z : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → (∃ (N : ℕ) (_ : 1 ≤ N) (κ : Type) (s : κ → H0 L N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i))) → ∀ (f g : Z ⟶ X) (v : LB.Iso (L.pull f) (L.pull g)), v.IsGen → (∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z) (j j' : L.ι), g z ∈ L.U j → f z ∈ L.U j' → Geo.Tor.gs g z _ (a.f (fun _ => j)) = (Geo.Tor.gw v (𝟙 Z) z j (fun _ => j') ^ n).val * Geo.Tor.gs f z _ (a.f (fun _ => j'))) → f = g := by
  intro X Z _ _ L hL hcov f g v _ hrel
  obtain ⟨N, hN, κ, s, hD, haff⟩ := hcov
  have fg : ∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z), f z ∈ nonzeroLocus a → g z ∈ nonzeroLocus a := by
    intro n hn a z hz
    obtain ⟨j', hj'⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus a hz
    obtain ⟨j, hj⟩ := exists_mem_chart' hL (g z)
    have hf' : f z ∈ L.U j' := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hj')
    have hgw : g z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => j) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hj
    have u2 : IsUnit (gs g z _ (a.f fun _ => j)) := by
      rw [hrel n hn a z j j' hj hf']
      exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen' f z _ hj')
    exact mem_nonzeroLocus_of_mem_basicOpen a j (mem_basicOpen_of_isUnit_gs g z _ hgw u2)
  have hW : ⨆ i, f ⁻¹ᵁ nonzeroLocus (s i) = ⊤ := by
    refine eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    have hz : f z ∈ ⨆ i, nonzeroLocus (s i) := by
      rw [hD]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, hi⟩
  refine (Z.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ nonzeroLocus (s i)) hW).hom_ext f g fun i => ?_
  show (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ f = (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ g
  refine ι_comp_eq_of_gs_eq f g (haff i) _ le_rfl (fun z hz => fg N hN (s i) z hz) fun a z hz => ?_
  have hfD : f z ∈ nonzeroLocus (s i) := hz
  have hgD : g z ∈ nonzeroLocus (s i) := fg N hN (s i) z hz
  obtain ⟨j, hb⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus (s i) hgD
  have hgj : g z ∈ L.U j := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hb)
  obtain ⟨j', hfj'⟩ := exists_mem_chart' hL (f z)
  obtain ⟨m, t, hm, ht⟩ := exists_sec_extend_pos hL (s i) a
  have step_before_last_eq_s_succ := hrel N hN (s i) z j j' hgj hfj'
  have eq_t := hrel (N * m) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) t z j j' hgj hfj'
  have ext_g := gs_pull_extend (s i) t a ht g z j hgD hgj
  have ext_f := gs_pull_extend (s i) t a ht f z j' hfD hfj'
  have hu : IsUnit (gs g z _ ((s i).f fun _ => j)) := isUnit_gs_of_mem_basicOpen' g z _ hb
  have key : gs g z _ ((s i).f fun _ => j) ^ m * gs g z _ a =
      gs g z _ ((s i).f fun _ => j) ^ m * gs f z _ a := by
    rw [← ext_g, eq_t, ext_f, step_before_last_eq_s_succ, mul_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
    ring
  exact ((hu.pow m).mul_left_cancel key).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_nonzeroLocus_of_universallyClosed {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y]
    [UniversallyClosed f] {H : LB X} {κ : Type} [Finite κ] (s : κ → H.Sec) (hcov : ⨆ j, nonzeroLocus (s j) = ⊤)
    (haff : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (t : H.Sec) : IsAffineOpen (nonzeroLocus t) := by
  classical
  have := Fintype.ofFinite κ
  choose r hr using fun j => AmpleSpan.exists_isRatio (s j) t
  choose σ hσ using fun j => AmpleSpan.exists_isRatio t (s j)
  have top := AmpleSpan.ker_sup_span_eq_top f s s hcov (fun j l => if l = j then 1 else 0)
    (fun j k => by simp [apply_ite]) t (AmpleSpan.isCompact_nonzeroLocus s hcov haff t) r hr
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_
  · have e := congrArg (Ideal.map (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t) le_top).hom r)) top
    rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
      (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq] at e
    convert e using 3
    funext j
    simp [apply_ite]
  · rintro _ ⟨j, rfl⟩
    rw [(hr j).basicOpen, inf_comm, ← (hσ j).basicOpen]
    exact (haff j).basicOpen _

theorem IsAmpleLB.isAffineOpen_nonzeroLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f]
    {L : LB X} (h : IsAmpleLB L) {n : ℕ} (hn : 1 ≤ n) (s : (lbPow L n).Sec) : IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨N, hN, H⟩ := h.exists_cover_mul
  obtain ⟨M, u, hu, ha⟩ := H n hn
  have := isAffineOpen_nonzeroLocus_of_universallyClosed f u hu ha (secCast (Nat.mul_comm n N) (secPow s N))
  rwa [nonzeroLocus_secCast, nonzeroLocus_secPow s hN] at this

theorem isAffineOpen_nonzeroLocus_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ (n : ℕ), 1 ≤ n → (∀ s : H0 L n, IsAffineOpen (nonzeroLocus s)) ∧ ∃ (m : ℕ) (_ : 1 ≤ m) (M : ℕ) (t : Fin M → H0 L (n * m)), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro R _ X _ L hL hA n hn
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨s', hs, -⟩ : ∃ s' : (lbPow L n).Sec, nonzeroLocus s' = nonzeroLocus s ∧ _ :=
      exists_sec_oneTerm L (K' := PUnit) rfl s
    exact hs ▸ h.isAffineOpen_nonzeroLocus X.hom hn s'
  · obtain ⟨N, hN, H⟩ := h.exists_cover_mul
    obtain ⟨M, u, hu, -⟩ := H n hn
    choose t ht using fun i => exists_sec_oneTerm L (K' := Fin 1) (e' := ((n * N : ℕ) : ℤ))
      (by rw [Nat.mul_comm]) (u i)
    exact ⟨N, hN, M + 1, t, (iSup_congr fun i => (ht i).1).trans hu⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionLiftAbelianPartFiniteExtensionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_abelianPart_finite_extension : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : W →+* F), Function.Injective φ ∧ φ.comp (algebraMap V W) = (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) ∧ IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧ IsLocalHom (algebraMap V W) ∧ (∀ z : F, z ^ N = 1 → z ∈ φ.range) ∧ ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), y ^ N = 1 ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (y).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) ∧ (Spec.map (CommRingCat.ofHom φ)) ≫ b.left = x.left := by
  first | exact @GlobalTheory.TorsionLift.torsion_lift | exact GlobalTheory.TorsionLift.torsion_lift | (intros; apply GlobalTheory.TorsionLift.torsion_lift <;> assumption)
end

