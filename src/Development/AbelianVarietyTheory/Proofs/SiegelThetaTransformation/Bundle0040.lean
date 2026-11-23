module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeSupOfCoprime
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPoints
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology

namespace GlobalTheory.RationalDiscrete

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nhds_zero_inclR :
    ∃ U ∈ 𝓝 (0 : AF F ⊗[F] E), ∀ x : E, inclR (F := F) (AF F) x ∈ U → x = 0 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop (F := F) (E := E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
  refine ⟨⋂ k, B.coord k ⁻¹' U, Filter.iInter_mem.2 fun k => ?_, fun x hx => ?_⟩
  · exact (hc k).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  · refine b.ext_elem fun k => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine h _ ?_
    have hk : B.repr ((1 : AF F) ⊗ₜ[F] x) k ∈ U := Set.mem_iInter.1 hx k
    rw [Algebra.TensorProduct.basis_repr_tmul] at hk
    simpa using hk

theorem discreteTopology_HFinIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    DiscreteTopology (HFinIn (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : HFinIn (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : HFinIn (AF F) σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin M) (Fin M) E) - 1 : Matrix (Fin M) (Fin M) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discreteTopology_GQ : ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) :=
  fun D V => discreteTopology_HFinIn D.sp.cm.sig V.gram

end GlobalTheory.RationalDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisensteinSeriesTermUnitaryGraph
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem kZero_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom)
    (h₂ : x₂ ∈ X.dom) (z₁ w : Fin n → Fin g → ℂ) : kZero X idx x₁ x₂ z₁ w ≠ 0 := by
  unfold kZero
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact inv_ne_zero (pow_ne_zero _ (mul_ne_zero (DblPoint.det_aLin_ne_zero h₁ h₂ τ)
    (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

private theorem isUn_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : IsUn X (1 : GL (Fin r) E) := by
  unfold IsUn
  intro x y
  simp

theorem eisTerm_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ γ : GL (Fin r) E, IsUn X γ → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ z₁ w : Fin n → Fin g → ℂ, kZero X idx x₁ x₂ z₁ w * eisTerm X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) = dbl X bas idx φ₁ (wG X bas idx γ φ₂) 0 * kZero X idx x₁ (lact γ x₂) z₁ w := by
  intro E _ _ _ r X g bas idx n hs hn γ hγ φ₁ φ₂ h₁ h₂ x₁ hx₁ x₂ hx₂ z₁ w

  obtain ⟨hsb₂, hth₂, -⟩ := wG_laws E r X g bas idx n hs hn γ hγ φ₂ h₂
  have hγx₂ : lact γ x₂ ∈ X.dom := IsUn.lact_mem hγ hx₂
  obtain ⟨hT, hZ', -⟩ := dblZ_mem_Hn E r X x₁ hx₁ (lact γ x₂) hγx₂
  have hZ : dblZ X x₁ x₂ ∈ Hn X.Ψ r := (dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂).2.1

  obtain ⟨hU, a, ha, hact⟩ := iota_act_dbl E r X g bas idx n hs hn 1 γ (isUn_one' X) hγ
  obtain ⟨hA, hzz⟩ := hact x₁ hx₁ x₂ hx₂
  have e1 : lact (1 : GL (Fin r) E) x₁ = x₁ := UnAct.lact_one' x₁
  simp only [e1] at hA hzz

  obtain ⟨hΦ, hΦd, -⟩ := DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  obtain ⟨hΦ', hΦ'd, -⟩ :=
    DblEx.dbl_spec E r X g bas idx n hs hn φ₁ (wG X bas idx γ φ₂) h₁ hsb₂
  obtain ⟨hW, hWT, -⟩ := _root_.GlobalTheory.SW.weil_action E X.Ψ hT n r hn (iota X 1 γ) hU (dbl X bas idx φ₁ φ₂) hΦ

  have key : ∀ u v : Fin n → Fin g → ℂ,
      thH X.Ψ (weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) =
        a * thH X.Ψ (dbl X bas idx φ₁ (wG X bas idx γ φ₂)) (dblZ X x₁ (lact γ x₂))
          (dblz X idx x₁ (lact γ x₂) u v) (dblz' X idx x₁ (lact γ x₂) u v) := by
    intro u v
    obtain ⟨hz, hz', hk⟩ := hzz u v
    have d1 := hΦd x₁ hx₁ x₂ hx₂ u v
    have d2 := hΦ'd x₁ hx₁ (lact γ x₂) hγx₂ u v
    have t2 : thA X bas idx (wG X bas idx γ φ₂) (lact γ x₂) = thA X bas idx φ₂ x₂ :=
      hth₂ x₂ hx₂
    rw [t2, d1] at d2
    have tw := hWT (dblZ X x₁ x₂) hZ (dblz X idx x₁ x₂ u v) (dblz' X idx x₁ x₂ u v)
    rw [hA, ← hz, ← hz'] at tw
    have hK' := kZero_ne_zero X idx hx₁ hγx₂ u v
    apply mul_left_cancel₀ hK'
    rw [tw, ← mul_assoc, hk, mul_assoc, d2]
    ring

  have hW' : weil X.Ψ (iota X 1 γ) (dbl X bas idx φ₁ φ₂) =
      a • dbl X bas idx φ₁ (wG X bas idx γ φ₂) := by
    refine (thH_summable_and_inj E X.Ψ hT n r _ hW _ hZ').2 _ ((_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ _ _ hΦ' hΦ').2.1 a) ?_
    intro z z'
    obtain ⟨u, v, rfl, rfl⟩ := DblEx.dblz_surj E r X g idx n x₁ hx₁ (lact γ x₂) hγx₂ z z'
    rw [key u v]
    unfold thH
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left]

  obtain ⟨-, -, hk⟩ := hzz z₁ w
  have hK := kZero_ne_zero X idx hx₁ hx₂ z₁ w
  have hH : hFac X.Ψ (iota X 1 γ) (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w)
      (dblz' X idx x₁ x₂ z₁ w) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    exact mul_ne_zero ha hK hk.symm
  unfold eisTerm
  rw [hW', Pi.smul_apply, smul_eq_mul, ← mul_inv_cancel_right₀ hH
    (kZero X idx x₁ (lact γ x₂) z₁ w), hk]
  field_simp

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GphiEqSmulPhiF
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GPhi

theorem finite_quot {G : Type} [AddCommGroup G] {A B C : AddSubgroup G} (hC : C.FG) (hA : A ≤ C) {m : ℕ}
    (hm : 0 < m) (h : ∀ y ∈ A, m • y ∈ B) : Finite (A ⧸ B.addSubgroupOf A) := by
  have h1 : (AddSubgroup.toIntSubmodule C).FG := (Submodule.fg_iff_addSubgroup_fg _).2 hC
  have h2 : (AddSubgroup.toIntSubmodule A).FG := h1.of_le hA
  have h3 : A.FG := (Submodule.fg_iff_addSubgroup_fg _).1 h2
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 h3
  refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact h y y.2

theorem finsum_exchange {Q C V : Type} [Finite Q] [Finite C] [AddCommGroup V] [Module ℂ V] (t : ℂ) (a : C → ℂ)
    (e : C → Q → ℂ) (f : Q → V) :
    ∑ᶠ q, (t * ∑ᶠ c, a c * e c q) • f q = t • ∑ᶠ c, a c • ∑ᶠ q, e c q • f q := by
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite C
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.mul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem natCast_mem_Mfr {H : Host E} (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod.symm.le.trans Ideal.mul_le_right
  exact h (Ideal.mem_span_singleton_self _)

theorem gphi_eq_smul_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n), IsSympl X bas → Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ (ρ : ℝ) (s : Lt E n → ℝ), 0 < ρ ∧ ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (v : TF n g), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → ∃ t : ℂ, ‖t‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, 0 < s Λ ∧ ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → gphi X bas (H.w0 : E) Λ L v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = (t * (s Λ : ℂ)) • phiF bas D (Mfr l) hn v₀ L Λ := by
  intro E _ _ _ H Dw l Xo c n d _ _ hF hlev ph ψ x₀ hpin r g X bas idx D hn hs hev hr tie v₀ hv₀ x0
  have hM0 : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM : (d.l₂.M : 𝓞 E) ∈ D.𝔪 := tie.m ▸ natCast_mem_Mfr d.l₂
  have := finite_levQ Dw d.l₂
  obtain ⟨ρ, s, hρ, hsv⟩ := ShVac.shift_vac E r X g bas idx n hs hev D _ hM0 hM v₀ hv₀
  have hcard : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
  refine ⟨Nat.card (Fin n → LevQ Dw d.l₂) * ρ, s, mul_pos (by exact_mod_cast hcard) hρ, ?_⟩
  intro L hL mk mk₂ δ v h1 h2 h12 hd hx hv
  rw [← tie.w] at hv ⊢
  obtain ⟨t₁, ht₁, H₁⟩ := GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum E H Dw l Xo c n d hF hlev ph ψ x₀ hpin r X D hn hr tie L hL mk mk₂ δ x0
    h1 h2 h12 hd hx
  obtain ⟨t₂, ht₂, H₂⟩ := hsv L hL v hv
  refine ⟨t₁ * (Nat.card (Fin n → LevQ Dw d.l₂) * t₂), by rw [norm_mul, norm_mul, ht₁, ht₂, Complex.norm_natCast, _root_.one_mul],
    fun Λ hΛ => ⟨(H₂ Λ hΛ).1, fun N hN Y hY => ?_⟩⟩
  obtain ⟨⟨u, hu⟩, -, hp, -⟩ := TensVac.vacua E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ
  have hfg := (GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hev D.w D.w_int D.w_tr L hL.1 _ Λ hΛ).1
  have hfin : Finite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _) := by
    refine finite_quot hfg ?_ hM0 (ShVac.nsmul_tens_right fun x hx => ?_)
    · intro y hy
      simpa using ShVac.nsmul_tens_right (Λ := Λ) (k := 1) (L' := L)
        (fun x hx => by simpa using Submodule.smul_le_right hx) y hy
    · rw [mul_comm _ D.𝔪, Submodule.mul_smul]
      exact Submodule.smul_mem_smul hM hx
  have hP := _root_.GlobalTheory.Dict.poisson_roots E H Dw d.l₂ r g X bas idx n hs hev D.w D.w_int D.w_tr L mk₂ hL.1 h2 Λ hΛ N hN Y hY
    (projA X bas D.w (tens Λ L) v) (by rw [hp v hv.1 u hu]; exact TensVac.sb_smul _ hu.1)
    (fun y hy => by rw [hp v hv.1 u hu, TensVac.heisG_smul, smul_comm, hu.2.2 y hy])
  rw [← tie.m] at hP
  have e := (H₂ Λ hΛ).2
  rw [Level.sh] at e
  unfold gphi phiF
  simp only [H₁ Λ hΛ N hN Y hY]
  rw [finsum_exchange]
  simp only [fun cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) => hP cl cl.2, e, TensVac.heisG_smul]
  have := Fintype.ofFinite (tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸
      (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _)
  simp only [finsum_eq_sum_of_fintype, Finset.smul_sum, smul_smul, Level.sh]
  refine Finset.sum_congr rfl fun cl _ => ?_
  congr 1
  ring

end GlobalTheory.Dict.GPhi
end

