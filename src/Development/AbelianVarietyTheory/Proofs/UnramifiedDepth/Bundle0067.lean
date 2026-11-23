module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeaf
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataUnramifiedLengthBoundStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearData_unramified_length_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ [IsLocalRing O], p ≠ 2 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e), (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a - (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ IsLocalRing.maximalIdeal O) → ∀ (rk : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (rk τ) → Fin d → O), (∀ τ, EigB ρG τ (W τ)) → ∀ j : Fin w.n, ∃ xs : NNReal, HasLen v O ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k))) xs ∧ v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) * (rk (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs := by
  first | exact @GlobalTheory.ChF.linDat_unram_bound | exact GlobalTheory.ChF.linDat_unram_bound | (intros; apply GlobalTheory.ChF.linDat_unram_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNLowerBoundBaseChange
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem nabValN_lower_bound_baseChange : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C) (R : Subring C), (∀ x, x ∈ R ↔ ((0 : ℝ) : WithTop ℝ) ≤ v x) → (∀ x : T.V, ((0 : ℝ) : WithTop ℝ) ≤ v (ι (algebraMap T.V T.Fr x))) → ∀ (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB T.Fr d O) (B' : FB C d O), (∀ i, B'.G.F i = MvPowerSeries.map ι (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ι (B.A.act a i)) → ∀ (h : PS T.Fr 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) [Fintype (Letter Ty r n)] (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (cp : Letter Ty r n → Fin n) (u : Letter Ty r n → Fin d → T.Fr) (ν : WithBot (WithTop ℝ)), (∀ P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a, ∀ f : PS T.Fr n d, IsIntPS T f → ν ≤ (WithBot.some (v (ι (nabValN B T.Fr h w0 m f cp u P))) : WithBot (WithTop ℝ))) → ∀ P ∈ HaO r n C R cc isX a, ∀ f : PS C n d, (∀ μ, ((0 : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff μ f)) → ν ≤ (WithBot.some (v (nabValN B' C (MvPowerSeries.map ι h) w0 m f cp (fun l j => ι (u l j)) P)) : WithBot (WithTop ℝ)) := by
  intro T C _ _ v ι R hR hV d O _ _ B B' hG hA h hh w0 m Ty _ r n _ cc isX a cp u ν hν P hP f hf
  obtain ⟨s, c, Q, hc, hQ, rfl⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n T.V T.Fr C ι R
    (fun x => (hR _).2 (hV x)) cc isX a P hP
  obtain ⟨-, -, hadd, hsm⟩ := GlobalTheory.nabValN_bilinear C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
  have hsum : ∀ (g : PS C n d) (F : Fin s → MvPolynomial (Letter Ty r n) C) (S : Finset (Fin s)),
      nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (∑ j ∈ S, F j)
        = ∑ j ∈ S, nabValN B' C (MvPowerSeries.map ι h) w0 m g cp (fun l j => ι (u l j)) (F j) := by
    intro g F S
    classical
    induction S using Finset.induction_on with
    | empty =>
      have := hsm 0 g 0
      simpa using this
    | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd, ih]
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.nabValN_eq_sum_coeff C d O B' (MvPowerSeries.map ι h) w0 m n
    (Letter Ty r n) cp (fun l j => ι (u l j))
    (∑ j, MvPolynomial.C (c j) * MvPolynomial.map ι (Q j))
  rw [hS f]
  induction ν using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe w =>
    refine WithBot.coe_le_coe.2 ?_
    refine v.map_le_sum fun μ _ => ?_
    rw [v.map_mul, hsum]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using hf μ))
    refine v.map_le_sum fun j _ => ?_
    rw [hsm, v.map_mul]
    refine le_trans ?_ (le_add_of_nonneg_left (by simpa using (hR _).1 (hc j)))
    have hmon : (MvPowerSeries.monomial μ (1 : C) : PS C n d)
        = MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n d) := by
      rw [MvPowerSeries.map_monomial, map_one ι]
    rw [hmon, GlobalTheory.nabValN_map T.Fr C ι d O B B' hG hA h hh w0 m n _ (Letter Ty r n) cp u (Q j)]
    refine WithBot.coe_le_coe.1 (hν (Q j) (hQ j) _ ?_)
    intro ρ
    classical
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOne
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

open Formalism.BaseCaseIdentities (Data Kn s0)

noncomputable section

namespace GlobalTheory.MainTerm

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem mm_neg_iff {x : C} : V.MM (-x) ↔ V.MM x := by
  unfold VF.MM
  rw [V.v.map_neg]

theorem chain_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) (s : ℕ) (hs : s < Kn i) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s * X.j' ∧
      IndepMod V (fun δ c => if D.lev c = s then chainMat D s c (em (cc δ)) else 0) := by
  haveI := X.algClosed
  induction s with
  | zero =>
    refine ⟨N, Function.Embedding.refl _, by omega, fun co _ hco ν => ?_⟩
    have := hco (em ν)
    simpa [hem, chainMat_zero] using this
  | succ s ih =>
    obtain ⟨m, cc, hm, hI⟩ := ih (by omega)
    have hsK : s < Kn D.i := by rw [h.2.2.1]; omega
    obtain ⟨m', cc', hm', hI'⟩ := _root_.GlobalTheory.SemilinearNullity.rank_nullity C V (I g) m X.j' (V.l ^ 2)
      (Nat.one_le_pow _ _ V.l_prime.pos)
      (fun δ c => if D.lev c = s + 1 then chainMat D (s + 1) c (em (cc δ)) else 0)
      (by
        intro δ c
        split_ifs
        · exact h.chainMat_int _ _ _
        · exact VF.Ge.zero 0)
      (by
        intro N' x hx hxI hxM
        refine _root_.GlobalTheory.ChainStep.rank_le C V d I J X hA g a hb i S Z D h s hs m
          (fun δ c => chainMat D s c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI N' x hx hxI ?_
        intro ν e he
        have := hxM ν e
        simpa [he, chainMat_succ, hsK, h.2.1] using this)
    exact ⟨m', cc'.trans cc, by rw [Nat.succ_mul]; omega, hI'⟩

theorem mainVec_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s0 i * X.j' ∧
      IndepMod V (fun δ => mainVec S D (em (cc δ))) := by
  have hi : Odd i := h.2.2.1 ▸ D.i_odd
  obtain ⟨m, cc, hm, hI⟩ := chain_rank X hA g a hb i S D h N em hem (s0 i) (chainStartIndex_lt_chainLength_of_odd hi)
  refine ⟨m, cc, hm, fun co hco hM => ?_⟩
  refine _root_.GlobalTheory.LastStep.indepMod_first_coeff C V d I J X hA g a hb i S Z D h (s0 i) (chainStartIndex_lt_chainLength_of_odd hi) m
    (fun δ c => chainMat D (s0 i) c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI co hco ?_
  intro κ
  have h1 := hM κ
  simp only [mainVec, h.2.2.1, h.2.1, chainStartIndex_lt_chainLength_of_odd hi, and_true] at h1
  rcases neg_one_pow_eq_or C (s0 i + 1) with h2 | h2
  · simpa [h2] using h1
  · rw [← mm_neg_iff]
    simpa [h2] using h1

theorem not_big_add_odd (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) {i : ℕ} (hi : Odd i) : ¬ X.big g (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    obtain ⟨e, he⟩ := hA.1
    have h2 : 2 ∣ d := ⟨e, by omega⟩
    have h3 : (a + (i : ZMod d)).val % 2 = (a.val + i) % 2 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2, Nat.add_mod,
        Nat.mod_mod_of_dvd _ h2, ← Nat.add_mod]
    obtain ⟨k, rfl⟩ := hi
    simp only [Nat.even_iff]
    omega
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · rw [hA.2, hpar, not_not]; exact (hA.2 a).1 hb
  · rw [h1, not_not, hA.2, hpar, ← hA.2]; exact (h1 a).1 hb

theorem both (X : RowData C V d I J) (hA : X.Alt) (h5 : 5 ≤ V.l) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d) (U : Fin X.n → I g → C)
    (U' : Fin X.n → I (1 - g) → C) (hU : X.SatIn g a U)
    (hU' : X.SatIn (1 - g) (a + (i : ZMod d)) U') :
    ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
      X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ ∧
        (i = 1 → X.MPlusConcl g a n0 e v' Φ) := by
  haveI := X.algClosed
  haveI := X.charZero
  obtain ⟨S, N1, D, hv, hl, hDi, hal, hty, hN1, A, hAint, hAeq⟩ :=
    _root_.GlobalTheory.AdaptedChain.adaptedChainData C V d I J X hA g a hb i hi hid U hU
  have h : Adapted S D a i := ⟨hv, hl, hDi, hal, hty⟩
  obtain ⟨m, c1, hm, hI1⟩ := mainVec_rank X hA g a hb i S D h N1 ⟨D.ι, D.ι_inj⟩ D.ι_lev
  have hΨint : ∀ c0 (u : I (1 - g) → C), (∀ k, V.Ge 0 (u k)) →
      V.Ge 0 (∑ κ : J g, ∑ k : I (1 - g), mainVec S D c0 κ * X.pair g κ k * u k) :=
    fun c0 u hu => VF.Ge.sum fun κ _ => VF.Ge.sum fun k _ =>
      ((h.mainVec_int c0 κ).mul_int (X.pair_int g κ k)).mul_int (hu k)
  obtain ⟨n0, c2, hn0, hI2⟩ := _root_.GlobalTheory.SemilinearNullity.rank_nullity C V (Fin X.n) m X.j 1 le_rfl
    (fun δ b => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (D.ι (c1 δ)) κ * X.pair g κ k * U' b k)
    (fun δ b => hΨint _ _ (hU'.1.1 b))
    (by
      intro N x hx hxI hxM
      refine _root_.GlobalTheory.PairCount.pair_kernel_le C V d I J X g _ (not_big_add_odd X hA g a hb hi) U' hU' N
        (fun ν κ => ∑ δ, x ν δ * mainVec S D (D.ι (c1 δ)) κ)
        (fun ν κ => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (h.mainVec_int _ _)) ?_ ?_ ?_
      · intro ν κ hκ
        simp [h.mainVec_pure _ κ hκ]
      · intro co hco hM
        refine hxI co hco (hI1 (fun δ => ∑ ν, co ν * x ν δ)
          (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) fun κ => ?_)
        convert hM κ using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      · intro ν b
        convert hxM ν b using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, pow_one]
        rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_comm)
  let em : Fin n0 ↪ I g := (c2.trans c1).trans ⟨D.ι, D.ι_inj⟩
  have hem : ∀ δ, D.lev (em δ) = 0 := fun δ => D.ι_lev _
  have hK : 0 < Kn i := by rw [Kn_eq hi]; omega
  have hemty : ∀ δ, (X.G g).ty (Sum.inl (em δ)) = a := fun δ => by
    rw [hty _ (by rw [hem]; exact hK), hem]; simp
  have hemal : ∀ δ x, S.al (em δ) 1 x = 0 := fun δ x =>
    h.al_one (D.pure_good _ (by rw [hem, hDi]; exact hK)) x
  obtain ⟨hn0n, Y, hYint, hYdet, hYΦ⟩ := _root_.GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod C V X.n n0
    (fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (em c) κ * X.pair g κ k * U' b k)
    (fun b c => hΨint _ _ (hU'.1.1 b)) hI2
  let v' : Fin X.n → I (1 - g) → C := fun b x => ∑ b', Y b b' * U' b' x
  have hv'int : ∀ b k, V.Ge 0 (v' b k) := fun b k =>
    VF.Ge.sum fun b' _ => (hYint b b').mul_int (hU'.1.1 b' k)
  have hv'ty : ∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0 :=
    fun b k hk => by simp [v', hU'.2 _ k hk]
  have hety : ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → S.tan (em c) x = 0 := fun c x hx =>
    tan_pure S _ x (by rw [hemty]; exact hx)
  have hS0 : ∀ g', Nonempty (Sys (X.G g')) := fun g' => by
    obtain ⟨S', -⟩ := sysExists (X.G g') (fun c x => if c = x then 1 else 0)
      (by intro c x; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0])
      (by
        intro c x hx
        rw [if_neg]
        rintro rfl
        exact hx rfl)
      (by
        have : (Matrix.of fun c x : I g' => if c = x then (1 : C) else 0) = 1 := by
          ext c x; simp [Matrix.one_apply]
        rw [this, Matrix.det_one, V.v.map_one])
    exact ⟨S'⟩
  obtain ⟨SS, rfl⟩ : ∃ SS : ∀ g', Sys (X.G g'), SS g = S :=
    ⟨Function.update (fun g' => (hS0 g').some) g S, by simp⟩
  choose t ht using fun g' => (tExistsUnique (X.G g') (SS g')).exists
  have hζ := _root_.GlobalTheory.MainTerm.zeta_leaf_main_term C V d (I g) (J g) (X.G g) (SS g) _ D a i h hid (t g) (ht g) n0 em hem
  refine ⟨n0, fun δ => (SS g).tan (em δ), v',
    fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec (SS g) D (em c) κ * X.pair g κ k * v' b k,
    ⟨⟨?_, hn0n⟩, isSat_tan _ em, ⟨fun c => A (c1 (c2 c)), fun c b => hAint _ b, fun c x => ?_⟩,
      ⟨Y, hYint, hYdet, fun b x => rfl⟩, fun b c => hΨint _ _ (hv'int b), fun b c hb => ?_, ?_,
      fun μ hμ => _root_.GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero C V d I J X g a i _ _ _ _ _ μ hμ⟩,
    ⟨SS g, t g, em, fun c => mainVec (SS g) D (em c), ht g, fun c => rfl, hemal,
      fun c κ => h.mainVec_int _ _, fun b c => rfl, hζ⟩, ?_⟩
  · have h1 := two_mul_chainStartIndex_add_one_of_odd hi
    rw [Kn_eq hi] at hN1
    have h2 : (i + 1) * X.j' = (s0 i + 1 + 1) * X.j' + s0 i * X.j' := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · exact ((SS g).cur_zero_inl _ x).symm.trans (hAeq _ x)
  · rw [← hYΦ b c hb]
    simp only [v', Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin X.n))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact _root_.GlobalTheory.MainTermWeight.weight_gauge_sub_main C V d I J X hA h5 g a i hi hid SS t ht n0 X.n _ v'
      (fun c => mainVec (SS g) D (em c)) hety hv'int hv'ty
      (_root_.GlobalTheory.LeafCoordWeight.weight_nonneg C V d (I g) (J g) (X.G g) (SS g) _ D a i h (t g) (ht g) n0 em hem) hζ
  · rintro rfl
    simp only [fun c => funext (h.mainVec_level_one (hem c))]
    exact _root_.GlobalTheory.MainTerm.mPlus_of_good_tangents C V d I J X hA hid g a SS t ht n0 em v' hemty hemal hv'int hv'ty

theorem main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  intro C _ V d _ I J _ _ X
  constructor
  · intro hA h5 g a hb i hi hid U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, -⟩ := both X hA h5 g a hb i hi hid U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2⟩
  · intro hA h5 hd g a hb U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, h3⟩ := both X hA h5 g a hb 1 odd_one hd U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2, h3 rfl⟩

end GlobalTheory.MainTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugate
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact _root_.GlobalTheory.RowLaw.cartHyp_of_rlaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p) (_root_.GlobalTheory.ProjSelf.hasProj_self C V O dd Y d I0 p)
      (_root_.GlobalTheory.hasTeich_selfData C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := _root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact _root_.GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)

end GlobalTheory.RowLaw
end

