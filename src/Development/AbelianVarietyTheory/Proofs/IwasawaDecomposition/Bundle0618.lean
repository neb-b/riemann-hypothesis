module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatHeckeBall


end GlobalTheory.RatHeckeBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HodgeInteriorGram

theorem isDerivAt0_comp_equiv {g g' : ℕ} {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (y : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem int_eq_of_exp_eq (m n : ℤ) (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m := by
    intro K hK
    obtain ⟨N, hN⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hK)
    have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ) := by
      push_cast
      linear_combination (norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN
      field_simp
      ring
    exact ⟨N, by exact_mod_cast e⟩
  have hz : n - m = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  omega

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ)
    (z w : Fin g → ℂ) : hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end GlobalTheory.HodgeInteriorGram

theorem GlobalTheory.HodgeInteriorGram.gram_eq_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs
  have hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀ := by
    rw [← hkx]; exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩
  have hg : ∀ τ, (hodgeMet Z U).gram x f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ) := fun τ => dif_pos hexf
  obtain ⟨k'', x'', hx'', hkx'', hv⟩ := GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec
  have hk : k'' = k := by
    apply hinj
    have e := x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))
    exact W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x')
      ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))
  subst hk
  have hu : W.F.u (W.ik k'') (W.Pm k'' x'') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k'' x'').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by
    rw [← hkx'']
    exact (Category.assoc _ _ _).symm
  have hper := W.period k'' x''
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k'' x'' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k'' x'' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left)
      (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs ⟨τ, b⟩
  have hmat := fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ'
    (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ)
    (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) (hder τ') (hwc τ) (hwc τ')
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · obtain ⟨h1, -⟩ := hmat τ τ
    rw [hg τ]
    have e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) =
        of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩)) := by
      ext b b'
      simp only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]
    rw [e2, h1]
    rcases Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0
    · ext b
      exact absurd b.2 (by omega)
    · have hdp := hdpos k'' x'' hx'' τ h0
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
  · have h2 := (hmat q.1 p.1).2 hpq q.2 p.2
    rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
    exact h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomogeneousComponentChernClassesOfRoots
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassComp

theorem esymm_isHomogeneous' (n k : ℕ) : (esymm (Fin n) ℝ k).IsHomogeneous k := by
  unfold esymm
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have h := IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin n) ℝ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℝ i)
  rw [Finset.sum_const, (Finset.mem_powersetCard.mp ht).2] at h
  simpa using h

theorem chernRoots_monomial_isHomogeneous {ι : Type} (m : ι → ℕ) (s : (ι × ℕ) →₀ ℕ) (c : ℝ) :
    (chernRoots m (monomial s c)).IsHomogeneous (Finsupp.weight Prod.snd s) := by
  rw [chernRoots, aeval_monomial, Finsupp.weight_apply, Finsupp.sum]
  have hc : (algebraMap ℝ (MvPolynomial (Root m) ℝ) c).IsHomogeneous 0 := isHomogeneous_C _ _
  have := hc.mul (IsHomogeneous.prod (s.support) (fun x => (rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)) ^ s x)
    (fun x => x.2 * s x) (fun x _ => ((esymm_isHomogeneous' (m x.1) x.2).rename_isHomogeneous).pow (s x)))
  simpa [Finsupp.prod, smul_eq_mul, mul_comm] using this

theorem homogeneousComponent_chernRoots {ι : Type} (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ) :
    homogeneousComponent d (chernRoots m Q) = chernRoots m (weightedHomogeneousComponent Prod.snd d Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [homogeneousComponent_of_mem (chernRoots_monomial_isHomogeneous m s c),
      weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end GlobalTheory.GrassComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFunctionMatrixRelation
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem exists_log_lift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (hz : ‖z‖ < 1 / 2) (h0 : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) :
    ∃ s ∈ logDom n a, logExp a s = z ∧ (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) ∧
      1 + ‖s‖ ≤ 5 * (1 + |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖|) := by
  classical
  set s : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k with hs
  have hzk : ∀ k, ‖z k‖ < 1 / 2 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz
  have hpos : ∀ k : Fin n, (k : ℕ) < a → 0 < ‖z k‖ := fun k hk => norm_pos_iff.mpr (h0 k hk)
  have hlogneg : ∀ k : Fin n, (k : ℕ) < a → Real.log ‖z k‖ < 0 := fun k hk =>
    Real.log_neg (hpos k hk) (by linarith [hzk k])
  set ℓ := |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖| with hℓ
  have hℓk : ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖z k‖ ≤ ℓ := by
    intro k hk
    rw [hℓ, norm_prod, Real.log_prod]
    · calc -Real.log ‖z k‖ ≤ ∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), -Real.log ‖z j‖ := by
            apply Finset.single_le_sum (f := fun j => -Real.log ‖z j‖)
            · intro j hj
              have := hlogneg j (Finset.mem_filter.mp hj).2
              linarith
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        _ = -∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), Real.log ‖z j‖ := by
            rw [Finset.sum_neg_distrib]
        _ ≤ _ := neg_le_abs _
    · intro j hj
      exact (hpos j (Finset.mem_filter.mp hj).2).ne'
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true, hs]
      rw [Complex.log_re]
      exact hlogneg k hk
    · simp only [hk, if_false, hs]
      linarith [hzk k]
  · funext k
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true, hs]
      exact Complex.exp_log (h0 k hk)
    · simp only [logExp, hk, if_false, hs]
  · intro j hj
    simp only [hj, if_true, hs]
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  · have hsk : ∀ k, ‖s k‖ ≤ ℓ + 4 := by
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [hk, if_true, hs]
        have h1 : ‖Complex.log (z k)‖ ≤ |(Complex.log (z k)).re| + |(Complex.log (z k)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have h2 : |Real.log ‖z k‖| = -Real.log ‖z k‖ := abs_of_neg (hlogneg k hk)
        have h3 := Complex.abs_arg_le_pi (z k)
        have h4 := hℓk k hk
        linarith [Real.pi_lt_four]
      · simp only [hk, if_false, hs]
        linarith [hzk k]
    have : ‖s‖ ≤ ℓ + 4 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr hsk
    linarith

theorem eventually_entries_le {V m n : Type} [TopologicalSpace V] [Fintype m] [Fintype n] {W : V → Matrix m n ℂ} {b₀ : V}
    (h : ContinuousAt W b₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ ≤ M := by
  classical
  have hij : ∀ i j, ∀ᶠ b in 𝓝 b₀, ‖W b i j‖ < ‖W b₀ i j‖ + 1 := by
    intro i j
    have hc : ContinuousAt (fun b => ‖W b i j‖) b₀ :=
      continuous_norm.continuousAt.comp ((continuous_id.matrix_elem i j).continuousAt.comp h)
    exact hc.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨∑ i, ∑ j, (‖W b₀ i j‖ + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have hall : ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ < ‖W b₀ i j‖ + 1 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hij i j
    filter_upwards [hall] with b hb i j
    calc ‖W b i j‖ ≤ ‖W b₀ i j‖ + 1 := (hb i j).le
      _ ≤ ∑ j', (‖W b₀ i j'‖ + 1) :=
          Finset.single_le_sum (f := fun j' => ‖W b₀ i j'‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖W b₀ i' j'‖ + 1) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖W b₀ i' j'‖ + 1))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem differentiableOn_finset_prod {V J : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {u : Finset J} {f : J → V → ℂ}
    {B : Set V} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) B) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) B := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i u)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.ShFam.Hor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMField
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.FaceIn

section Lattice

variable {X : Type} [AddCommGroup X]

theorem inRCone_of_nsmul_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {c : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * γ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * β a b = ∑ i, (c i : ℝ) * γ i a b := by exact_mod_cast h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_right_inj' hk', h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  obtain ⟨c, hc, e⟩ := hβ
  have e1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at e1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hc j) (show (0 : ℝ) ≤ h (γ j) by exact_mod_cast hcut.1 j)).1 e1.symm
  have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
    have hne : (h (γ j) : ℝ) ≠ 0 := fun h0 => hj ((hcut.2 j).1 (by exact_mod_cast h0))
    exact (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
  refine ⟨fun i => c (s i), fun i => hc _, ?_⟩
  rw [e]
  classical
  rw [← Finset.sum_map Finset.univ s (fun j => c j • toReal (γ j))]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

theorem apply_eq_zero_of_genRank_le {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' → Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h0 : ∀ j, h (γ (s j)) = 0) (hr : genRank γ ≤ genRank fun j => γ (s j))
    (j : Fin m) : h (γ j) = 0 := by
  unfold genRank at hr
  set B := Submodule.span ℤ (Set.range γ) with hB
  set A := Submodule.span ℤ (Set.range fun j => γ (s j)) with hA
  haveI : Module.Finite ℤ B := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  have hAB : A ≤ B := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨s j, rfl⟩)
  have hAk : A ≤ LinearMap.ker h := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
  set K : Submodule ℤ B := LinearMap.ker (h.domRestrict B) with hK
  have h1 : Module.finrank ℤ A ≤ Module.finrank ℤ K := by
    rw [← (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq]
    exact Submodule.finrank_mono fun y hy => hAk hy
  have h2 := Submodule.finrank_quotient_add_finrank K
  have h3 : Module.finrank ℤ (B ⧸ K) = 0 := by omega
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h3
    (Submodule.Quotient.mk ⟨γ j, Submodule.subset_span ⟨j, rfl⟩⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at e
  have e' : a * h (γ j) = 0 := by simpa [hK] using e
  exact (mul_eq_zero.1 e').resolve_left ha

end Lattice

theorem apply_eq_of_inRCone {O : Type} [CommRing O] {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : ψ.LinearOn γ) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (γ i) : ℝ) = N * ψ.evalZ (γ i)) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) : (ℓ β : ℝ) = N * ψ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff ψ γ).1 hγ c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem inRCone_of_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms H.bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone (bar := H.bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β + x] ![1] (by simp [hs])
        (by simpa using hsp) (by simp)
    obtain ⟨S, -, hcov⟩ := (hψ X hX).finite
    obtain ⟨e, mm, γ, c, hγ, -, hc, hsum⟩ := hcov _ hR
    refine ⟨_, mm, fun i => pull e.symm.toLinearMap (γ i), CarDim.isCell_pull_equiv hγ e.symm, ⟨c, hc, ?_⟩, rfl⟩
    exact LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply] using this
  obtain ⟨n, γ, hγ, hγs, hrk⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨N', ℓ', hN', h1', h2', h3'⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have e0 := apply_eq_of_inRCone hγ.linear h1 hγs
  rw [map_add (f := _), Int.cast_add, hadd, mul_add] at e0
  have eβ : (N : ℝ) * ψ.evalZ β = ℓ β := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have ex : (N : ℝ) * ψ.evalZ x = ℓ x := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have hγβ : InRCone γ β := by
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hβp eβ
    exact inRCone_of_nsmul_eq hk hc
  obtain ⟨cx, -, hcx⟩ : InRCone γ x := by
    obtain ⟨k, c, hk, hc⟩ := h3 x hx hxp ex
    exact inRCone_of_nsmul_eq hk hc
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (N : ℤ) • ℓ' - (N' : ℤ) • ℓ with hh
  have happ : ∀ u, (h u : ℝ) = N * ℓ' u - N' * ℓ u := fun u => by simp [hh]
  let Z : Finset (Fin n) := Finset.univ.filter fun j => h (γ j) = 0
  let s : Fin Z.card ↪ Fin n := (Z.orderEmbOfFin rfl).toEmbedding
  have hcut : IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have : (0 : ℝ) ≤ h (γ j) := by
        rw [happ, h1]
        have := mul_le_mul_of_nonneg_left (h2' _ (hγ.mem j) (hγ.nonneg j)) hNr.le
        linarith
      exact_mod_cast this
    · have : Set.range s = Z := Z.range_orderEmbOfFin rfl
      rw [this]
      simp [Z]
  have hface := isCell_face_of_isFaceCut E H q ψ hψ X hX hD n γ hγ _ s h hcut
  have hβ0 : h β = 0 := by
    have : (h β : ℝ) = 0 := by
      rw [happ, apply_eq_of_inRCone hv.linear h1' hvβ, ← eβ]; ring
    exact_mod_cast this
  have hle : genRank γ ≤ genRank fun j => γ (s j) := by
    rw [hlab X hX _ hs hsp, hlab X hX _ hβ hβp, Nat.cast_inj] at hl
    rw [hrk, hl]
    exact Nat.sInf_le ⟨_, _, hface, inRCone_face hcut hγβ hβ0, rfl⟩
  have hall := apply_eq_zero_of_genRank_le (h := h) (fun j => (hcut.2 _).2 ⟨j, rfl⟩) hle
  have hx0 : (h x : ℝ) = 0 := by
    rw [apply_eq_of_toReal_eq hcx h]
    simp [hall]
  rw [happ, ← ex] at hx0
  have ex' : (N' : ℝ) * ψ.evalZ x = ℓ' x := by
    have : (N : ℝ) * (N' * ψ.evalZ x - ℓ' x) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_left hNr.ne']
  obtain ⟨k, c, hk, hc⟩ := h3' x hx hxp ex'
  exact inRCone_of_nsmul_eq hk hc

end GlobalTheory.PolFan.Mark.FaceIn
end
end

