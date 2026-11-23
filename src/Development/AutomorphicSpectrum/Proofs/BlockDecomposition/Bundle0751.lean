module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import GroundTheory.GlobalFields.TateThesis.LocalConductor

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyConjDiagonal
section
open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

namespace GlobalTheory.CompanionTheory.UnitarySide

theorem charpoly_conj_diagonal {K : Type} [Field K] {n : ℕ} (c D g : GL (Fin n) K) (d : Fin n → K)
    (hD : D.val = Matrix.diagonal d) (hg : g = c * D * c⁻¹) :
    g.val.charpoly = ∏ i, (X - C (d i)) := by
  subst hg
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hD,
    Matrix.charpoly_diagonal]

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.CompanionTheory.UnitarySide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedOfFunctor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem closed_of_functor (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (near : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t :=
  GlobalTheory.T.affine_ideal_locus_criterion Y P stab loc (_root_.GlobalTheory.CompanionTheory.TrivLoc.Rep.exists_ideal_on_affine Y P stab loc near)

theorem locus_near {S : Scheme.{0}} {A Y : Over S} [GrpObj A] (hA : IsAbelianScheme A) [IsLocallyNoetherian Y.left]
    {N : LB (A ⊗ Y).left} (hN : N.IsLB) (y : Y.left) :
    ∃ (U : Y.left.Opens) (hU : IsAffineOpen U) (r : Γ(Y.left, U)) (I : Ideal Γ(Y.left, U)), y ∈ Y.left.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y.left, U) →+* R'), IsUnit (g r) →
        (Locus N (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨p, hp⟩ := hU.range_fromSpec.ge hy
  have : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨X, f, M, hM, h₁, h₂, h₃, h₄, h₅, h₆, H⟩ := _root_.GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family S A Y hA N hN Γ(Y.left, U) hU.fromSpec
  obtain ⟨r, I, hr, H'⟩ := _root_.GlobalTheory.CompanionTheory.TrivLoc.exists_ideal_near _ X f M hM h₁ h₂ h₃ h₄ h₅ h₆ p
  refine ⟨U, hU, r, I, ?_, fun R' _ g hg => ?_⟩
  · rw [← hU.fromSpec_image_basicOpen]
    exact ⟨p, hr, hp⟩
  · have hq := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
    exact (H R' g _ _ _ hq).symm.trans (H' R' g _ _ _ hq hg)

theorem trivLocus : TrivLocus := by
  intro S A Y _ hA hY N hN h1
  obtain ⟨Z, i, hi, H⟩ := closed_of_functor Y.left (fun T t => Locus N t)
    (fun T T' h t ht => ht.comp h) (fun T t h => _root_.GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally S A Y hA N hN h1 T t h) (locus_near hA hN)
  refine ⟨Over.mk (i ≫ Y.hom), Over.homMk i rfl, hi, fun T y => ?_⟩
  refine (locus_left_iff y).symm.trans ((H _ y.left).trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨Over.homMk z (by simp [reassoc_of% hz]), by ext; simpa using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.left, by simpa using congrArg (fun q => q.left) hz⟩

end GlobalTheory.CompanionTheory.TrivLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactLevelExists
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open GlobalTheory.PrincCong (congSub mem_congSub_iff isOpen_congSub exists_mat_subset)
open GlobalTheory.LFun.ConjPlace (invT invT_val mem_iff_invT map_mem_Ov_iff)
open GlobalTheory.ThetaSatake (cw cloc)
open GlobalTheory.CompanionTheory.ThetaSatPair (embT_cw invT_symm)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KExLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le_KGL (w : Pl E) (n k : ℕ) : congSub w n k ≤ KGL w (n := n) :=
  fun g hg => ((mem_congSub_iff w n k g).1 hg).1

theorem eventually_congSub_le (w : Pl E) (a : ℕ) (U : Subgroup (GLw a w)) (hU : IsOpen (U : Set (GLw a w))) :
    ∀ᶠ k in atTop, congSub w a k ≤ U := by
  have hVn : (U : Set (GLw a w)) ∈ 𝓝 (1 : GLw a w) := hU.mem_nhds U.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hVn
  obtain ⟨t, htn, htV⟩ := Filter.mem_comap.1 hVn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 htn
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨N₀, hN₀⟩ := exists_mat_subset w a (Filter.inter_mem hA hB')
  filter_upwards [eventually_ge_atTop N₀] with m hm γ hγ
  have a1 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 hγ).2
  have a2 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 (inv_mem hγ)).2
  exact htV (hAB ⟨a1.1, a2.2⟩)

theorem continuous_detGL (w : Pl E) (a : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw a w → (w.adicCompletion E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · have e : (fun g : GLw a w => (((GeneralLinearGroup.det g)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
        fun g => ((g⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) _).det := by
      funext g
      rw [← map_inv]
      rfl
    exact e ▸ Continuous.matrix_det (Units.continuous_val.comp continuous_inv)

theorem eventually_det (w : Pl E) (a : ℕ) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) :
    ∀ᶠ k in atTop, ∀ g ∈ congSub w a k, μ (GeneralLinearGroup.det g) = 1 := by
  have hU : IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw a w)) : Set (GLw a w)) :=
    hμ.preimage (continuous_detGL w a)
  filter_upwards [eventually_congSub_le w a _ hU] with k hk g hg
  exact hk hg

theorem isCompact_congSub (w : Pl E) (n k : ℕ) : IsCompact (congSub w n k : Set (GLw n w)) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w n k)) (congSub_le_KGL w n k)

theorem blocks_mem_congSub {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) {k : ℕ} (hg : blk h w m X ∈ congSub w n k) :
    m.1 ∈ congSub w a k ∧ m.2 ∈ congSub w b k := by
  obtain ⟨hK, hc⟩ := (mem_congSub_iff w n k _).1 hg
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have v := GlobalTheory.CompanionTheory.CtS.blk_val_eq h w m X
  have iv := GlobalTheory.CompanionTheory.CtS.blk_inv_val h w m X
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have v11 : ∀ i j, (blk h w m X).val (e (Sum.inl i)) (e (Sum.inl j)) = m.1.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have v22 : ∀ i j, (blk h w m X).val (e (Sum.inr i)) (e (Sum.inr j)) = m.2.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have i11 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inl i)) (e (Sum.inl j)) = (m.1⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have i22 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inr i)) (e (Sum.inr j)) = (m.2⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have o11 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inl i)) (e (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  have o22 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inr i)) (e (Sum.inr j)) =
      (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(mem_congSub_iff w a k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩,
    (mem_congSub_iff w b k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩⟩
  · rw [← v11]; exact h1 _ _
  · rw [← i11]; exact h2 _ _
  · rw [← v11, ← o11]; exact hc _ _
  · rw [← v22]; exact h1 _ _
  · rw [← i22]; exact h2 _ _
  · rw [← v22, ← o22]; exact hc _ _

theorem conj_mem_congSub (w : Pl E) (n k : ℕ) {x g : GLw n w} (hx : x ∈ KGL w (n := n)) (hg : g ∈ congSub w n k) :
    x * g * x⁻¹ ∈ congSub w n k := by
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y * z⁻¹, (MonoidHom.normal_ker _).conj_mem y hy z, by simp only [map_mul, map_inv]⟩

theorem invT_mem_congSub {u w : Pl E} (c : u.adicCompletion E ≃+* w.adicCompletion E)
    (hc : ∀ x, Valued.v (c x) = Valued.v x) (a k : ℕ) {g : GLw a u} (hg : g ∈ congSub u a k) :
    invT c a g ∈ congSub w a k := by
  have h1 := (mem_congSub_iff u a k _).1 hg
  have h2 := (mem_congSub_iff u a k _).1 (inv_mem hg)
  refine (mem_congSub_iff w a k _).2 ⟨(mem_iff_invT c (map_mem_Ov_iff c hc) g).1 h1.1, fun i j => ?_⟩
  have e : (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      c ((1 : Matrix (Fin a) (Fin a) (u.adicCompletion E)) j i) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  rw [invT_val, e, ← map_sub, hc]
  exact h2.2 j i

theorem under_cw (w : Pl E) :
    (cw w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) (cw w) w).2
    (Or.inr (conjPl_conjSrc _ w))).symm

end GlobalTheory.CompanionTheory.KExLevel

namespace GlobalTheory.CompanionTheory.KExLevel

theorem kEx : KEx := by
  intro E _ _ _ n Sec _ R _ μ hμ L hL
  let T : Finset (Pl E) := R ∪ R.image cw
  have A : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ R, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k → m ∈ L a w := by
    intro a ha w hw
    obtain ⟨L₁, L₂, e, l1, l2⟩ := hL a (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)) w hw
    filter_upwards [eventually_congSub_le w a L₁ l1.1, eventually_congSub_le w (n - a) L₂ l2.1] with k h1 h2 m m1 m2
    rw [e]
    exact ⟨h1 m1, h2 m2⟩
  have B : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ T, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k →
        μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 := by
    intro a _ w _
    filter_upwards [eventually_det w a (μ w) (hμ w), eventually_det w (n - a) (μ w) (hμ w)] with k h1 h2 m m1 m2
    rw [map_mul, map_pow, map_pow, h1 _ m1, h2 _ m2, one_pow, one_pow, one_mul]
  obtain ⟨M, hA, hB⟩ := (((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (A a ha)).and ((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (B a ha))).exists
  have hT : ∀ w, w ∈ T → (if w ∈ T then congSub w n M else KGL w (n := n)) = congSub w n M := fun w hw => if_pos hw
  refine ⟨fun w => if w ∈ T then congSub w n M else KGL w (n := n), ⟨fun w => ?_, ?_⟩, fun w => ?_, fun w hw => ?_,
    fun a ha w hw m X hm => ?_, fun a ha w hw hs u hc m X hm => ?_⟩
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isOpen_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
  · refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    refine hw ?_
    have h' : w ∉ T := h
    simp only [if_neg h']
    exact le_rfl
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isCompact_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  · refine if_neg fun h => ?_
    rcases Finset.mem_union.1 h with h | h
    · exact hw w h rfl
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact hw r hr (under_cw r).symm
  · have hwT : w ∈ T := Finset.mem_union_left _ hw
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos hwT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ w m X hm
    exact ⟨hA a ha' w hw m b1 b2, hB a ha' w hwT m b1 b2⟩
  · have hu : u = cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
    have huT : u ∈ T := Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, hu.symm⟩)
    have hw' : w = cw u := by rw [hu]; exact (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos huT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ u m X hm
    clear hu hc
    subst hw'
    have hv : ∀ x, Valued.v ((cloc u).symm x) = Valued.v x := fun x => by
      have := (GlobalTheory.CuspRep.conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 ((cloc u).symm x)
      have e : GlobalTheory.CuspRep.conjLoc (IsCMField.complexConj E).toRingEquiv u ((cloc u).symm x) = x :=
        (cloc u).apply_symm_apply x
      rw [e] at this
      exact this.symm
    let p : ∀ c : ℕ, GLw c u → GLw c (cw u) := fun c g =>
      (invT (cloc u) c).symm ((PhiU c (u.adicCompletion E))⁻¹ * g * PhiU c (u.adicCompletion E))
    have hp : ∀ c (g : GLw c u), g ∈ congSub u c M → p c g ∈ congSub (cw u) c M := fun c g hg => by
      have hk : (PhiU c (u.adicCompletion E))⁻¹ ∈ KGL u (n := c) := inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ c)
      have h1 := conj_mem_congSub u c M hk hg
      rw [inv_inv] at h1
      change (invT (cloc u) c).symm _ ∈ _
      rw [invT_symm]
      exact invT_mem_congSub (cloc u).symm hv c M h1
    have he : ∀ c (g : GLw c u), embW c u g = embT c (cw u) (p c g) := fun c g => by
      rw [embT_cw]
      simp only [p, MulEquiv.apply_symm_apply]
      congr 1
      group
    exact ⟨hB a ha' u huT m b1 b2, (p a m.1, p (n - a) m.2), hA a ha' (cw u) hw _ (hp _ _ b1) (hp _ _ b2),
      he _ _, he _ _⟩

end GlobalTheory.CompanionTheory.KExLevel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCj
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwUFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

end GlobalTheory.CompanionTheory.IwUFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypersurfaceComplexPointsMeasurableNull
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ

section ZeroLocus

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} [IsIntegral X] {i : X ⟶ MP ℤ m n}

theorem mem_ptsIn_preimage_mchart (c : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ↔
      PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

theorem ev_dehomog_eq_zero_iff (c : ∀ k, Bk n k) {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c))
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder (PtsOver.map i rfl _ y) z) :
    ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0 ↔
      eval z (map (Int.castRingHom ℂ) f) = 0 := by
  have hw := (mem_ptsIn_preimage_mchart c y).1 hy
  have hne : ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
    pow_ne_zero _ ((hz k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hw))
  rw [CxPts.ev_app i rfl, _root_.GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder m n c f a hf _ z hz hw, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right hne, Or.inl⟩

theorem zeroLocus_eq_iUnion [IsClosedImmersion i] {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} =
    ⋃ c : ∀ k, Bk n k, {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
      ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, h0⟩
    have hc : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀
        (i ⁻¹ᵁ mchart fun k => ptChart ((PtsOver.map i rfl _ y).1 (IsLocalRing.closedPoint ℂ)) k) :=
      (mem_ptsIn_preimage_mchart _ y).2 (CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k))
    exact ⟨_, hc, (ev_dehomog_eq_zero_iff _ hf y hc hz).2 h0⟩
  · rintro ⟨c, hc, h0⟩
    obtain ⟨z, -, hz⟩ := _root_.GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder m n X i y
    exact ⟨z, hz, (ev_dehomog_eq_zero_iff c hf y hc hz).1 h0⟩

theorem measurableSet_ev_eq_zero {Y : Scheme.{0}} (q : Y ⟶ Sp ℤ) (W : Y.Opens) (g : Γ(Y, W)) :
    MeasurableSet {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} := by
  have hS : IsOpen (ptsIn q σ₀ W) := isOpen_ptsIn W
  have hO : IsOpen (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) :=
    (continuousOn_ev g).isOpen_inter_preimage hS isOpen_compl_singleton
  have e : {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} =
      ptsIn q σ₀ W \ (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  rw [e]
  exact hS.measurableSet.diff hO.measurableSet

end ZeroLocus

theorem zeroLocus_measurable_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a → f ∉ ptIdeal (i (genericPoint X)) →
    MeasurableSet {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} ∧
    ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹'
      {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  intro m n X _ i _ D f a hf hI
  rw [zeroLocus_eq_iUnion hf]
  refine ⟨MeasurableSet.iUnion fun c => measurableSet_ev_eq_zero _ _ _, fun ch => ?_⟩
  rw [Set.preimage_iUnion, Set.inter_iUnion]
  refine measure_iUnion_null fun c => ?_
  by_cases hg : genericPoint X ∈ i ⁻¹ᵁ mchart c
  · exact _root_.GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf X (i ≫ mpStr ℤ m n) σ₀ D ch _ hg _ (_root_.GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal m n X i c hg f a hf hI)
  · have e : ch.e.target ∩ ch.e.symm ⁻¹' {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
        ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun v hv => hg
        (((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2
          ⟨_, trivial, CxPts.mem_ptsIn.1 hv.2.1⟩)
    rw [e, measure_empty]

end GlobalTheory.CompanionTheory.MixZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuCharacterExists
section
noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuOpen

theorem isOpen_ker_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen ((χ.loc w).ker : Set (w.adicCompletion L)ˣ) :=
  GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (χ.loc w)
    (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))

theorem unrChar_apply_of_isUnitAt {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (α : ℂˣ)
    (x : (w.adicCompletion L)ˣ) (hx : IsUnitAt w x) : GlobalTheory.SmGL.unrChar (w.adicCompletion L) α x = 1 := by
  rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion]
  have hx' : Valued.v (x : w.adicCompletion L) = 1 := hx
  rw [hx']
  simp

end GlobalTheory.CompanionTheory.MuOpen


open GlobalTheory.CompanionTheory.MuOpen in
theorem GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  intro h E _ _ _ hU
  obtain ⟨μ, e, hμ⟩ := h E hU
  refine ⟨μ, e, hμ, fun w hw x hx => ?_, GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ |>.1, fun w => isOpen_ker_loc μ w⟩
  rw [hμ.2.2.1 w hw]
  exact unrChar_apply_of_isUnitAt w _ x hx

end
end

