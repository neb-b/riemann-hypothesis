module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedUnitariesMovingBottomTriples
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfCongMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LabUniq

section Lin
variable {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem eq_of_congMod (x y : M) (h : ∀ m : ℕ, 1 ≤ m → CongMod m x y) : x = y := by
  let b := Module.Free.chooseBasis ℤ M
  rw [← sub_eq_zero]
  apply b.repr.injective
  ext k
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (b.repr (x - y) k).natAbs + 1 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := h N (by omega)
  have hxy : x - y = N • w := by rw [hw]; abel
  have h2 : b.repr (x - y) k = (N : ℤ) * b.repr w k := by
    rw [hxy, map_nsmul]; simp [nsmul_eq_mul]
  refine Int.eq_zero_of_abs_lt_dvd ⟨_, h2⟩ ?_
  rw [Int.abs_eq_natAbs]; omega

end Lin

section Diag
variable {Y : Type} [AddCommGroup Y]

theorem act_unit (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

end Diag

theorem qW_single {Y : Type} [AddCommGroup Y] (W : Matrix (Fin 8) (Fin 8) ℤ) (β : LinearMap.BilinForm ℤ Y) (y : Y) :
    qW W β (Pi.single 0 y) = W 0 0 * β y y := by
  unfold qW
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ κ : c.T.D.toPre.X ≃+ c.T.D.toPre.X, (∀ a b, c.T.β (κ a) (κ b) = c.T.β a b) ∧ ∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (fun a => κ (μ a)) := by
  intro g n F W Z i X ε hdiag p _ z c yy yy' h1 h2
  obtain ⟨θ, hq, hl, hE⟩ := _root_.GlobalTheory.GeomCore.main g n F W Z i X ε hdiag p z c yy yy' h1 h2
  have hc : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b :=
    fun E v => eq_of_congMod _ _ fun m hm => hE m hm E v
  let κ0 : c.T.D.toPre.X →+ c.T.D.toPre.X :=
    (Pi.evalAddMonoidHom (fun _ : Fin 8 => c.T.D.toPre.X) 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => c.T.D.toPre.X) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ hc v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  let κ := AddEquiv.ofBijective κ0 ⟨inj, surj⟩
  have hκ : ∀ x, κ x = κ0 x := fun x => rfl
  have hd : ∀ x, c.T.β (κ0 x) (κ0 x) = c.T.β x x := by
    intro x
    have := hq (Pi.single 0 x)
    rw [hsingle, qW_single, qW_single] at this
    exact mul_left_cancel₀ (X.diag_pos 0).ne' this
  refine ⟨κ, ?_, ?_⟩
  · intro a b
    rw [hκ, hκ]
    have hab := hd (a + b)
    simp only [map_add (f := _), LinearMap.map_add₂, LinearMap.add_apply] at hab
    have s1 := c.T.symm (κ0 a) (κ0 b)
    have s2 := c.T.symm a b
    have ha := hd a
    have hb := hd b
    linarith
  · intro x μ h
    rw [hl x μ h]
    congr 1
    funext a
    exact hθ μ a

end GlobalTheory.Poinc.LabUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGrids
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

theorem bottom_infExp_gap : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro _ i j
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := by
    show (G.V (.grid (i : ℕ) (j : ℕ))).rank % 2 = _
    rw [(node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).rank]
    rfl
  refine ⟨fun τ => -(D.hc τ).e ⟨j, j.2⟩ + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2),
    fun τ => (cen D 1 τ (D.R.m - i) : ℚ) + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2), fun t τ => ⟨?_, ?_, ?_⟩⟩
  · have h := GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, hε] at h
    exact h
  · have h := GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps] at h
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps, hε] at h
    exact h
  · have key := GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen (D := D) 1 τ i j i.2 j.2
    have hle : SqNum.botBig D i j + SqNum.botSmall D i j ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
      simp only [SqNum.botBig, SqNum.botSmall]
      omega
    have hle' : ((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast hle
    push_cast at key hle' ⊢
    linarith

end GlobalTheory.BotDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTuple
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem nuH_inv_eq_one {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) (u : (AE D)ˣ)
    (hu : IntU D u) (h : (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t)) :
    (nuH G t i j)⁻¹.1 (finIdl D u) = 1 := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one, div_eq_mul_inv]; exact mul_right_comm _ _ _
  have h0 := GlobalTheory.BotPairSmall.CondNu.nuH_inv_eq_one_of_cong hL G i j u hu (hatId_mono (modT_mul_conj_le G t) h)
  have h1 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu h
  rw [e, mul_inv]
  change ((nuH G μ₀ i j)⁻¹.1 * (L.xiH t)⁻¹.1) (finIdl D u) = 1
  rw [MonoidHom.mul_apply, h0, one_mul]
  change ((L.xiH t).1 (finIdl D u))⁻¹ = 1
  rw [h1, inv_one]

theorem conj_isCoprime_halfDifferent {I : Ideal (𝓞 D.host.E)}
    (h : IsCoprime I (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)})) : IsCoprime (D.host.conj • I) D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  have h2 : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ M := GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb)
  obtain ⟨a, ha, b, hb', e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
  have e1 := congrArg (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj) e
  rw [map_add (f := _), map_mul, map_natCast, map_one] at e1
  refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e1]
  exact M.add_mem (hle (Ideal.mem_sup_left (Ideal.smul_mem_pointwise_smul D.host.conj _ _ ha))) (M.mul_mem_left _ h2)

theorem modT_isCoprime_two_q {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (modT G t) (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) := by
  classical
  unfold modT
  refine IsCoprime.mul_left ?_ (IsCoprime.prod_left fun w hw => ?_)
  · obtain ⟨N, hN, hm⟩ := GlobalTheory.FunObj.StdDatum.HalfDiff.exists_nat_mem_condE G.pl ⟨hpq, hpq'⟩
    obtain ⟨x, y, e⟩ : IsCoprime ((N : ℕ) : 𝓞 D.host.E) ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) := Nat.Coprime.cast hN
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, ← e]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hm))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
    have hP : w ∈ L.Q t := hw.1.resolve_left hw.2
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := w.isMaximal.eq_of_le hne le_sup_left
    have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal :=
      heq.symm.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    refine (hL.Q_off t w hP).1 ?_
    rw [show D.host.QS * D.host.q * D.host.d * D.sp.T = (D.host.QS * D.host.q) * (D.host.d * D.sp.T) by ring, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h2q

theorem conj_modT_isCoprime_halfDifferent {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q)) (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (G : GridData L sc) (t : T) : IsCoprime (D.host.conj • modT G t) D.host.𝔟 :=
  conj_isCoprime_halfDifferent (modT_isCoprime_two_q hL hpq hpq' G t)

theorem smallPair_exists_tw : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.NormSum.Inp D → L.Is μ₀ → Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (G : GridData L sc) (t : T) {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ (i j : Fin D.R.m) (χα : HeckeU D (botSmall D i j)), (∀ x, χα.f x = (alphaH L t i j).1 (finIdl D x)) → ∀ (χν : HeckeU D (botBig D i j + botSmall D i j)), (∀ x, χν.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) → (∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χν.n τ) → ∃ P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl * Qn G t), P'.a = botSmall D i j ∧ P'.d = botBig D i j + botSmall D i j ∧ HasChars P' (alphaH L t i j) (nuH G t i j)⁻¹ ∧ IsStdDatum P' (D.host.conj • modT G t) (botBig D i j) ∧ IsBlockLevel P' (modT G t) (botBig D i j) := by
  intro D T L sc μ₀ _ hL hpq hpq' G t δ t0 hc ht i j χα hα χν hν hn
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have hd : Even (botBig D i j + botSmall D i j) :=
    ⟨halfRank D i j - (D.R.m - (j + 1)) / 2 - (D.R.m - j) / 2, by omega⟩
  obtain ⟨e0, hv, h0⟩ := GlobalTheory.Vacuum.exists_vacuum D ⊤ δ hc t0 ht (botSmall D i j) (botBig D i j + botSmall D i j)
    (hd.mul_left _)
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := GlobalTheory.FinWeil.exists_weil_of_vacuum D ⊤ δ hc _ _ e0 hv.1 h0 χα χν
  have hm := modT_ne_bot G t
  have hcop := GlobalTheory.SqTop.modT_sup_conj hL G t
  have hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (modT G t * D.host.conj • modT G t) →
      W.chV'.f u = 1 := by
    intro u hu h
    rw [hW2, hν, nuH_inv_eq_one hL G t i j u hu h]
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.CongReps.exists_reps D (botSmall D i j) _ (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  have hTT := GlobalTheory.BotPairSmall.cvec_conj_mem_TT D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hK := _root_.GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl
  have hS := GlobalTheory.StdSumFix.stdSum_fix_eig D δ _ _ e0 W _ _ hTT hK R hR1 hR2
  have hN := absNorm_modT G t
  have hidx := GlobalTheory.BotPairSmall.blockJ_relIndex D (modT G t) hm (botBig D i j) (botBig D i j + botSmall D i j)
  have hQ : 1 ≤ levQ G.pl * Qn G t := by
    rw [← hN]; exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 hm)
  have heig : ∀ h ∈ GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j), ∃ c : ℂ, ‖c‖ = 1 ∧
      W.Om 1 h (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
        (botBig D i j + botSmall D i j) e0)) = c • ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t)
          (botBig D i j) (botSmall D i j) (botBig D i j + botSmall D i j) e0) := by
    intro h hh
    obtain ⟨k, hk, c, hc1, e⟩ := _root_.GlobalTheory.BotPairSmall.cvec_eig D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop hcond (botBig D i j) rfl h hh
    exact ⟨c, hc1, hS.2 h k c hk e⟩
  refine ⟨{
      crv := hc, pt0 := ht, a := botSmall D i j, d := botBig D i j + botSmall D i j, a_le := Nat.le_add_left _ _,
      d_even := hd, e0 := e0, vac := hv, W := W,
      n := fun τ => ((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat, wt := ?_,
      F := ∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • modT G t) (botBig D i j) (botSmall D i j)
      (botBig D i j + botSmall D i j) e0),
      pres := _root_.GlobalTheory.BotPairSmall.pres_conj_std D δ t0 hc ht _ _ hd e0 hv W hW3 hW4 _ hm hcop (conj_modT_isCoprime_halfDifferent hL hpq hpq' G t) hcond (botBig D i j) rfl _ hN R hR1 hR2,
      fix := hS.1,
      J := GlobalTheory.BotPairSmall.blockJ D (modT G t) (botBig D i j) (botBig D i j + botSmall D i j),
      J_le := GlobalTheory.BotPairSmall.blockJ_le _ _ _ _,
      idx_ne := hidx.1,
      idx_le := hidx.2.trans (by rw [hN]; exact Nat.pow_le_pow_right hQ (by omega)),
      eig := heig }, rfl, rfl, ⟨fun x => ?_, fun x => ?_⟩, ⟨R, hR1, hR2, rfl⟩,
    fun h => GlobalTheory.BotPairSmall.blockJ_mem_iff_blockSet _ _ _ _ h⟩
  · intro τ
    show 2 * (((χν.n τ - ((botBig D i j + botSmall D i j : ℕ) : ℤ)) / 2).toNat : ℤ) = W.ep' * W.chV'.n τ - _
    rw [hW4, hW2]
    obtain ⟨r, hr⟩ := χν.par τ
    have := hn τ
    omega
  · show W.chV.f x ^ W.ep = _
    rw [hW3, zpow_one, hW1, hα]
  · show W.chV'.f x ^ W.ep' = _
    rw [hW4, zpow_one, hW2, hν]

end GlobalTheory.BotPairSmallTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => _root_.GlobalTheory.BotUnitMove.move_elts W i j A A' WW X Y hX hY t
  have hC := fun t => _root_.GlobalTheory.BotFrames.factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => _root_.GlobalTheory.BotFrames.move_fst W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => _root_.GlobalTheory.BotFrames.isThetaAt_stdSnd_move W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := _root_.GlobalTheory.BotTranslate.translate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBases
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixGlob


open TopologicalSpace in
theorem lc_props {Rg : Type} [CommRing Rg] [IsNoetherianRing Rg] {N : ℕ} {X H : Scheme.{0}}
    (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (i : H ⟶ X) [IsClosedImmersion c] [IsOpenImmersion i] :
    QuasiCompact (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    IsSeparated (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    LocallyOfFiniteType (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
  refine ⟨?_, inferInstance, ?_⟩
  · have h1 : NoetherianSpace (Sp (MvPolynomial (Fin N) Rg)) :=
      inferInstanceAs (NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin N) Rg)))
    have h2 : NoetherianSpace H :=
      ((i ≫ c).isEmbedding).isInducing.noetherianSpace
    exact (quasiCompact_iff_compactSpace _).2 inferInstance
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show (algebraMap Rg (MvPolynomial (Fin N) Rg)).FiniteType
      exact RingHom.finiteType_algebraMap.2 inferInstance
    infer_instance

theorem exists_homFixRep_of_secBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨N, X, c, H, i, AH, _, BH, _, φA, φB, Φ, hc, hi, pA, pB, hΦ, hiso, hrep⟩ :=
    GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs Rg A B L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨q1, q2, q3⟩ := lc_props c i
  exact ⟨HomFixRep.mk H (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))))
    AH BH φA φB pA pB Φ hΦ hiso (_root_.GlobalTheory.EndLoc.HomFixGlue.rep_of_affine _ A B L M hL hM H _ AH BH φA φB Φ pA pB hrep), q1, q2, q3⟩

end GlobalTheory.HomFixGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem exists_obj_extend_of_isPIsog : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  intro p _ D R _ b N _ _ c V K _ _ _ _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨-, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  have hcomm := o.ab.comm
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V K o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  exact exists_obj V K v _ rfl o₀' B φB hB hφB

end GlobalTheory.UPel.HT.ES.IsogDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (exact GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (intros; apply GlobalTheory.HTQuot.exists_representing_family_of_level_structure <;> assumption)
end

