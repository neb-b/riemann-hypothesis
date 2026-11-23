module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RawSeriesMoveDatum
section
section Point

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

theorem move_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → ∀ (wq wq' : (Fin n → LevQ Dw l) → c.F), (∀ q q', LevMoves h q q' → wq' q' = wq q) → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq' (actLat h Λ) b' N' (pushLet c h P) y v' → ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) ≠ 0 ∧ v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  intro wq wq' hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq' b' v' hv'
  obtain ⟨_, -, hproj⟩ := _root_.GlobalTheory.Phase.Proj.proj_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := _root_.GlobalTheory.Dict.RootsMove.roots_move E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq' q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      _root_.GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  refine ⟨?_, ?_⟩
  · rw [index_Ln, ← hrr]
    exact (Nat.pos_of_mul_pos_left (lt_of_lt_of_eq hz2 (zCard_eq _ hN' r))).ne'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt

namespace GlobalTheory.DatumMove

theorem move_complex (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : ℂ, ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ 1 N P y v →
        ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' → v = z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, ht1, ht⟩ := GlobalTheory.Phase.ChangePt.move_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL
    hrow nab hnab Λ h hU hh hT hT'
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht1
  refine ⟨((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)), fun y v v' hv hv' => ?_⟩
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa
    w 1).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1).1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ 1 N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 hP w' _ 1 N' u' hu')
  obtain ⟨hA', k3⟩ := ht x L y₀ F hx hSD w w' hw N N' hN hN' a P hPa 1 1 u u' one_ne_zero one_ne_zero hu hu'
  have hsq : ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA'))).ne'
  have k4 : u = ((Real.sqrt (A : ℝ) : ℝ) : ℂ) / (t * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ)) * u' := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ht0 hsq)]
    simp only [map_one, _root_.mul_one] at k3
    linear_combination -k3
  rw [k1, k2, k4]; ring

theorem exists_move_const (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l)
    [StarRing (𝓞 E)] (nab : NabV Xo c) (h1 : 1 ≤ Dw.p + Dw.q) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (w w' : (Fin n → LevQ Dw l) → c.F)
    (hw : ∀ q q', LevMoves h q q' → w' q' = w q) (N N' : ℕ) (hN : Λ.LevOK N l.M)
    (hN' : (actLat h Λ).LevOK N' l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hPa : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    ∃ z : c.F, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S),
      ShortValAt Xo c nab w Λ 1 N P y v →
        ∃ v', ShortValAt Xo c nab w' (actLat h Λ) 1 N' (pushLet c h P) y v' ∧ v = algebraMap c.F S z * v' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c h1 n hn
  obtain ⟨z, hid⟩ := @move_complex E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h hU hh hT hT' w w' hw N N' hN hN' a P hPa
  have hP := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1 P hPa
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  have ex1 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w 1
  have ex2 := GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN'
    a _ hP w' 1
  choose u hu using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex1.1 S y).exists
  choose u' hu' using fun (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => (ex2.1 S y).exists
  have n1 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u S y) = u T y' :=
    fun S T _ _ _ _ φ y y' hy => ex1.2 S T φ y y' hy _ _ (hu S y) (hu T y')
  have n2 : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
      (y : FrPt Xo c S) (y' : FrPt Xo c T), FrMap φ y y' → φ (u' S y) = u' T y' :=
    fun S T _ _ _ _ φ y y' hy => ex2.2 S T φ y y' hy _ _ (hu' S y) (hu' T y')
  have h : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = z * @u' ℂ _ s.toAlgebra y :=
    fun y => hid y _ _ (@hu ℂ _ s.toAlgebra y) (@hu' ℂ _ s.toAlgebra y)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : c.F, ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra,
      @u ℂ _ s.toAlgebra y = s z₀ * @u' ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u' ℂ _ s.toAlgebra y = 0
    · refine ⟨1, fun y => ?_⟩
      rw [h y, h0 y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @GlobalTheory.ConstRatio.ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u' ℂ _ s.toAlgebra) (@u ℂ _ s.toAlgebra)
        (@n2 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@n1 ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z h y hy
      have hz₀' : s z₀ = z := hz₀
      exact ⟨z₀, fun y => by rw [hz₀', h y]⟩
  have hfin := GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s u (fun S _ _ y => algebraMap c.F S z₀ * u' S y) n1
    (fun S T _ _ _ _ φ y y' hyy => by rw [map_mul, φ.commutes, n2 S T φ y y' hyy]) hz₀
  refine ⟨z₀, fun S _ _ y v hv => ⟨u' S y, hu' S y, ?_⟩⟩
  rw [(ex1.1 S y).unique hv (hu S y)]
  exact hfin S y

end GlobalTheory.DatumMove

end Point

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DatumMove


set_option maxHeartbeats 1000000 in
theorem rawSeries_move_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → ∀ x0 x1 : Fin n → LevQc Dw l, Submodule.span (𝓞 E) (Set.range x0) = ⊤ → Submodule.span (𝓞 E) (Set.range x1) = ⊤ → {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)} ⊆ (Submodule.span c.F {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x1)) La N P y (f p y)} : Set (Formalism.L2.Pj.Rul Xo c)) := by
  intro E _ _ _ H Dw l Xo c _ nab h1 _ hnab bad n a hbad hdom x0 x1 hx0 hx1 f ⟨hf, Λ, N, P, hU, hT, hM, hN, hP, hv⟩
  obtain ⟨γ, hγ, hb, hm, hw⟩ := exists_unitary_moving c (bad := 2 * bad) (by omega) x0 x1 hx0 hx1
  have triv : ∀ d, d ∣ 2 * bad → (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ ⟨stdLat E n⟩).TrivAt d := fun d hd => by
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk.coprime_dvd_right hd, h⟩
  obtain ⟨N', hN'⟩ := exists_levOK (triv 2 (Dvd.intro _ rfl)) hN
  have hM' := trivAt_act hm hM
  obtain ⟨z, hz⟩ := exists_move_const E H Dw l Xo c nab h1 hnab n hdom.2 Λ γ hU hγ hM hM' _ _ hw N N' hN hN' a P hP.1
  obtain ⟨k1, -, -, k2⟩ := (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a γ hγ).2 Λ
  by_cases hz0 : z = 0
  · have : f = 0 := by
      funext p y
      obtain ⟨v', -, e⟩ := hz p.R y _ (hv p y)
      rw [e, hz0, map_zero, zero_mul]
      rfl
    rw [this]
    exact Submodule.zero_mem _
  · have e : f = z • z⁻¹ • f := by
      funext p y
      change f p y = z • z⁻¹ • f p y
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hz0, map_one, one_mul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Submodule.smul_mem _ _ hf, _, N', _, k1 hU,
      trivAt_act (triv bad (Dvd.intro_left _ rfl)) hT, hM', hN', k2 P hP, fun p y => ?_⟩)
    obtain ⟨v', hv', e⟩ := hz p.R y _ (hv p y)
    have e2 : (z⁻¹ • f) p y = v' := by
      change z⁻¹ • f p y = v'
      rw [e, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul]
    rw [e2]
    exact hv'

end GlobalTheory.DatumMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid
noncomputable section

namespace GlobalTheory.RouteSeesaw

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.MixModel

theorem data_theta {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ.support,
      IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, φ₁, φ₂, hloc, -⟩, rfl, -⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vX_is (i : ℕ) ((j : ℕ) + 1) i.2 j.2).2.theta
  have v2 := (ρ.vT_is t ((i : ℕ) + 1) (j : ℕ) i.2 j.2).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem dagger_zero {D : D7} (S T : HSp D) : dagger S T 0 = 0 := by
  simp [dagger]

theorem hecke_mul' {D : D7} {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) :
    IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem splitFac_ratio {D : D7} (a b c : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    (splitFacO a c⁻¹ x y : ℂ) * (splitFacO b⁻¹ c⁻¹ x y : ℂ)⁻¹ = ((a y * b y : Circle) : ℂ) := by
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, Circle.coe_mul, Circle.coe_inv]
  have h1 : ((c x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h2 : ((b y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

theorem seesaw_product {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {Wo V V₁ : HSp D}
    {c1S c1T c2S c2T : (AE D)ˣ →* Circle}
    {ω₁ : GA D (negSp Wo) × GA D V →* Module.End ℂ (WO (negSp Wo) V → ℂ)}
    {ω₂ : GA D V₁ × GA D Wo →* Module.End ℂ (WO V₁ Wo → ℂ)}
    (H1 : IsWeilDatumO ψ (negSp Wo) V c1S c1T ω₁) (H2 : IsWeilDatumO ψ V₁ Wo c2S c2T ω₂)
    {f₁ : WO (negSp Wo) V → ℂ} {f₂ : WO V₁ Wo → ℂ} (hf₁ : IsThetaFunO ψ (negSp Wo) V f₁)
    (hf₂ : IsThetaFunO ψ V₁ Wo f₂) (g : GA D V) (g₁ : GA D V₁) :
    ∃ (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep Wo X), IsWeil ψ true Wo X χ χ' ω ∧
      X.rank = V.rank + V₁.rank ∧ ∃ Φ : WO (sgn true Wo) X → ℂ, IsThetaFunO ψ (sgn true Wo) X Φ ∧
        ∃ (h : GA D X) (c : ℂ), ∀ u, ω₁ (negGA Wo u, g) f₁ 0 * ω₂ (g₁, u) f₂ 0 = c * thetaKO ω u h Φ := by
  have hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η :=
    (GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩

  have H2b : IsWeilDatumO ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ (conjSource (conjAdjoint ω₂)) :=
    GlobalTheory.ConjWeil.weil_conjSource D ψ Wo V₁ _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V₁ Wo _ _ ω₂ H2)

  obtain ⟨ω₂c, H2c⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) V₁ c1S c2S⁻¹ hη H1.hecS
    (GlobalTheory.ConjWeil.hecke_inv H2.hecS) H1.resS (resEta_inv H2.resS)

  obtain ⟨⟨X, o⟩⟩ := GlobalTheory.OrthSumExists.exists_orthDec D V V₁
  obtain ⟨ω', H'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ (negSp Wo) X c1S (c1T * c2S⁻¹) hη
    H1.hecS (hecke_mul' H1.hecT (GlobalTheory.ConjWeil.hecke_inv H2.hecS)) H1.resS (o.rank_add ▸ resEta_mul H1.resT (resEta_inv H2.resS))
  have TT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ (X) V V₁ o (negSp Wo)

  have hF₂ : IsThetaFunO ψ (negSp Wo) V₁ (cj id (cj (dagger Wo V₁) f₂)) := by
    have h1 : IsThetaFunO ψ Wo V₁ (cj (dagger Wo V₁) f₂) := ((_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ V₁ Wo).2.2.1 f₂).2 hf₂
    have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ Wo V₁
    exact ((I.1 _).2).2 h1
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D V₁ g₁
  let ω : WRep Wo (X) := ω'.comp ((negGA Wo).toMonoidHom.prodMap (MonoidHom.id _))
  have hω : ω.toSgn true = ω' := MonoidHom.ext fun p => rfl
  refine ⟨X, c1S, c1T * c2S⁻¹, ω, ?_, o.rank_add.symm, o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂)),
    TT.box_theta _ _ hf₁ hF₂, o.emb (g, g₁), ((c1S y * c2T y : Circle) : ℂ)⁻¹, fun u => ?_⟩
  · show IsWeilDatumO ψ (sgn true Wo) _ _ _ (ω.toSgn true)
    rw [hω]; exact H'
  · obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (negSp Wo) (negGA Wo u)
    have k1 := TT.om_box c1S c1T c2S⁻¹ ω' ω₁ ω₂c H' H1 H2c (negGA Wo u) g g₁ f₁ _ hf₁ hF₂
    have k2 := GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ (negSp Wo) V₁ c2T⁻¹ c2S⁻¹ c1S c2S⁻¹ _ ω₂c H2b H2c
      (negGA Wo u) g₁ x y hx hy _ hF₂
    have k3 : conjSource (conjAdjoint ω₂) (negGA Wo u, g₁) (cj id (cj (dagger Wo V₁) f₂)) 0 = ω₂ (g₁, u) f₂ 0 := by
      rw [GlobalTheory.ConjWeil.conjSource_apply]
      simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
      rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_zero]
    show _ = _ * ω' (negGA Wo u, o.emb (g, g₁)) (o.boxT (negSp Wo) f₁ (cj id (cj (dagger Wo V₁) f₂))) 0
    rw [k1, OrthDec.boxT_zero, k2, Pi.smul_apply, smul_eq_mul, k3, splitFac_ratio]
    have h0 : ((c1S y * c2T y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp

end GlobalTheory.RouteSeesaw


open GlobalTheory.RouteSeesaw in
theorem GlobalTheory.FunObj.routeBig_kernel_product_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ'),
    ∀ d ∈ Θ.support, ∀ (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))),
      ∃ (ε : Bool) (X : HSp D) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep (G.V (.grid (i + 1) (j + 1))) X),
        IsWeil W.ψ ε _ X χ χ' ω ∧ X.rank = (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank ∧
        ∃ Φ : WO (sgn ε (G.V (.grid (i + 1) (j + 1)))) X → ℂ, IsThetaFunO W.ψ (sgn ε _) X Φ ∧
          ∃ (h : GA D X) (c : ℂ), ∀ u, W.kerA (.right i (j + 1)) d.1.2 g u * W.kerA (.down t (i + 1) j) d.2 u g₁ =
            c * thetaKO ω u h Φ := by
  intro D T L sc G μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
  obtain ⟨hf₁, hf₂⟩ := data_theta W B ρ t i j hΘ d hd
  have hp1 : (Pair.chi (i : ℕ) ((j : ℕ) + 1) : Pair T).InRange D.R.m := ⟨by omega, by omega⟩
  have hp2 : (Pair.mu t ((i : ℕ) + 1) (j : ℕ)).InRange D.R.m := ⟨by omega, by omega⟩
  obtain ⟨X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩ :=
    seesaw_product W.ψ_std (W.om_is _ hp1) (W.om_is _ hp2) hf₁ hf₂ g g₁
  exact ⟨true, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, hc⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeTranslateUnitVectorVacuumExpansio
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.TransExp

theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    Hf D T y x = (starRingEnd ℂ) (Hf D T x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wd_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ)
    (z : VC D N N') : Wd D T x (Wd D T y F) z = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Wd D T y (Wd D T x F) z := by
  have key : Complex.exp (-(Real.pi : ℂ) * Hf D T x y) =
      Formalism.MainNotions.TaylorLogMetric.kap D T x y * Complex.exp (-(Real.pi : ℂ) * Hf D T y x) := by
    rw [Formalism.MainNotions.TaylorLogMetric.kap, ← Complex.exp_add, hf_swap D T x y]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  have e1 : ∀ u v c : ℂ, Complex.exp (-(Real.pi : ℂ) * (u + v) - c) =
      Complex.exp (-(Real.pi : ℂ) * u - c) * Complex.exp (-(Real.pi : ℂ) * v) := by
    intro u v c; rw [← Complex.exp_add]; congr 1; ring
  simp only [Wd, U, VacMove.hf_add_left]
  rw [show z + y + x = z + x + y from add_right_comm _ _ _, e1 (Hf D T z y) (Hf D T x y),
    e1 (Hf D T z x) (Hf D T y x), key]
  ring

theorem wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type*} (x : VC D N N') (c : ℂ) (s : Finset ι)
    (f : ι → VC D N N' → ℂ) (z : VC D N N') :
    Wd D T x (fun w => c * ∑ q ∈ s, f q w) z = c * ∑ q ∈ s, Wd D T x (f q) z := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem wd_iop_of (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (e0 : VC D N N' → ℂ)
    (x : VC D N N') (hB : ∀ y ∈ B, ∀ F, Wd D T y F = fun z => al D T y * U D T y F z)
    (hfix : Wd D T x e0 = e0) :
    Wd D T x (Iop D T A B e0) = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Formalism.MainNotions.TaylorLogMetric.kap D T x ((Quotient.out q : B) : VC D N N') *
        Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
  have hI : Iop D T A B e0 = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
    funext z
    unfold Iop
    congr 1
    refine finsum_congr fun q => ?_
    rw [hB _ (Quotient.out q).2]
  funext z
  rw [hI]
  by_cases h0 : (A.addSubgroupOf B).index = 0
  · simp [Wd, U, h0]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    rw [wd_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [wd_comm, hfix]

theorem wd_iop_expand : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), Wd D (tor0 D ⊤ δ) x (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = fun z => ((Real.sqrt (((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index : ℝ))⁻¹ : ℂ) * ∑ᶠ q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) * Wd D (tor0 D ⊤ δ) ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) e0 z := by
  intro D δ hc 𝔪 h𝔪 a d e0 he x hx
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D a), _root_.GlobalTheory.SkewLatSD.skewLat_sd D 𝔪 d h𝔪, rfl⟩
  exact wd_iop_of D _ _ _ e0 x (_root_.GlobalTheory.ThetaLine.theta_line D h1 ⊤ δ hc a d _ kp).2.1 (VacMove.wd_fix h1 hc k0 he hx)

end GlobalTheory.FunObj.TransExp
end
end

