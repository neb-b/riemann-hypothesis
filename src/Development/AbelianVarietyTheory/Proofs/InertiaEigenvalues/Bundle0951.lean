module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0950
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatVectorsTwistedWeil
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistSeriesConj


set_option maxHeartbeats 4000000 in
theorem conj_series_twisted : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κw v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → PhaseTie T R κw v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → FixDat B τ → ∀ (ω ω' : PairRep (Vc D i) (Wc D i)) (ψ ψ' : Twist D Circle) (t t' : T0), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' → ψ.Good → ψ'.Good → B.admitted ψ.Q → IsTupOf R B ψ t → IsTupOf R B ψ' t' → ConjChar τ ψ ψ' → ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κw i) τ ζ (ph i • series B.F ω (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) (ph i • series B.F ω' (B.vecFlat ψ') h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κw v₀ O ph hnV hC hT0 hFW hio hQG i hOP hPT c hc u hu B hB hBo τ hτ hfix ω ω' ψ ψ' t t'
    hω hω' hψ hψ' hQ ht ht' hcc
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κw v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (_root_.GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hCI D G Pl0 T0 A T R F κw v₀ hC hTie hio O i hOP)).1
  obtain ⟨ζ0, hζ0, hgb⟩ := _root_.GlobalTheory.ConjTwist.FlatSeries.conj_flat_series hCI D G Pl0 T0 A T R F κw v₀ O ph hnV hC hT0 ⟨fw⟩ hio hQG i hOP hPT c hc u hu τ hτ
  have hQ' : B.admitted ψ'.Q := by rw [hcc.1]; exact hQ
  obtain ⟨f, hf⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t).1
  obtain ⟨f', hf'⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A _ R F hC hQG i t').1
  obtain ⟨s, hs⟩ := hgb t t' (conjTup_of R ht ht' hcc hfix) f f' hf hf'
  set ζ := ζ0 * ((R.xi t' s : Circle) : ℂ) with hζd
  have hζ : ζ ≠ 0 := by
    obtain ⟨n, hn, hpow⟩ := hζ0
    refine mul_ne_zero (fun h0 => ?_) (Circle.coe_ne_zero _)
    rw [h0, zero_pow hn.ne'] at hpow
    exact zero_ne_one hpow
  have hL := hC.lev
  obtain ⟨n, hn, hod⟩ := hL.xi_fin t'
  have hxn : (R.xi t' s : Circle) ^ n = 1 := GlobalTheory.OneCover.xi_pow_eq_one D (R.xi t') _ (hL.xi t') n hod s
  have hxc : ((R.xi t' s : Circle) : ℂ) ^ n = 1 := by
    have := congrArg (fun z : Circle => (z : ℂ)) hxn
    simpa using this
  have hroot : IsRoot1 ζ := by
    obtain ⟨m, hm, hpow⟩ := hζ0
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [hζd, mul_pow, pow_mul, hpow, one_pow, one_mul, pow_mul', hxc, one_pow]
  obtain ⟨hfin, ⟨k, hk⟩, hsum⟩ := GlobalTheory.FlatVecSum.vecFlat_eq_sum D G Pl0 T0 A _ R F hC i B hB hBo
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  obtain ⟨hk0, -⟩ := hsum k fun p => (hk p).1
  choose g0 hg0 using hk0
  have hlift : ∀ p, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm (g0 p))) (k p) := fun p => by
    exact (congrArg (fun z => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) z (k p))
      (R.eG.apply_symm_apply (g0 p))).mpr (hg0 p)
  have hrt : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∀ p, ConjFun (O i) (κw i) τ ζ
      (fun g => ph i * ser R i t f u h (c x) (g * k p)) (fun g => ph i * ser R i t' f' u h (c x') (g * k p)) :=
    fun h hh x x' hx p => GlobalTheory.ConjGen.conjFun_mul_right (O i) (κw i) hτ hE (hlift p) hζ (hs h hh x x' hx)
  have hcp : ∀ p, τ ((((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ)) = (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) := fun p => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix.2.1 p]
  have hx₀ : ConjVec i τ (0 : VsV D i ℂ) 0 := by
    unfold ConjVec
    simp
  have hCF0 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hs 1 (one_mem _) 0 0 hx₀)
  refine ⟨ζ, hroot, fun h hh x x' hx => ?_⟩
  have e1 : (ph i • series B.F ω (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) =
      fun g => ∑ p, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * (ph i * ser R i t f u h (c x) (g * k p)) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ConjGen.series_weil hB hQ hω (hBo.isWeil hC.thP.ωP ht),
      GlobalTheory.ConjGen.series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ hQ ht hf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : (ph i • series B.F ω' (B.vecFlat ψ') h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) =
      fun g => ∑ p, τ (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) * (ph i * ser R i t' f' u h (c x') (g * k p)) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.ConjGen.series_weil hB hQ' hω' (hBo.isWeil hC.thP.ωP ht'),
      GlobalTheory.ConjGen.series_vecFlat_eq_sum hC hB hBo k (fun p => (hk p).1) hψ' hQ' ht' hf', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hcp]
    ring
  rw [e1, e2, GlobalTheory.ConjClassSum.conjFun_iff]
  exact GlobalTheory.ConjGen.cf_sum hζ hCF0 _ _ _ fun p => (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 (hrt h hh x x' hx p)

end GlobalTheory.TwistSeriesConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [Algebra O O'] [AddCommGroup V]
  [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]


end Lin

section Onto
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

end Onto

section Comparison₂
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Comparison₂

section Tie2
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Tie2

section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Main

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((_root_.GlobalTheory.TwUnit.isKsForm_and_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact _root_.GlobalTheory.RankDescent.fullRk_of_spanGood D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (_root_.GlobalTheory.TwInputs.spanGood_of_sumOnto D Y.Z.ρ Y.Z.good Y.Z.rd i (_root_.GlobalTheory.RankOnto.sumOnto_of_goodRange D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemGfCOfSuppAtIdem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

noncomputable section

namespace GlobalTheory.ConjSpan

set_option autoImplicit false

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

def RelConj : Prop := ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
  Expands M κ (fun _ => 0) a f → Expands M κ (fun _ => 0) (fun k => τ (a k)) f

variable {M κ τ}

theorem expands_conj_swap (hz : RelConj M κ τ) (ζ : ℂ) {Φ Ψ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ} {b : Fin m → ℂ}
    {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {f' : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (h1 : Expands M κ Φ a f) (h2 : Expands M κ Φ b f') (hΨ : Expands M κ Ψ (fun k => ζ * τ (a k)) f) :
    Expands M κ Ψ (fun k => ζ * τ (b k)) f' := by
  have h0 : Expands M κ (fun _ => 0) (Fin.append a fun k => -b k) (Fin.append f f') := by
    intro g
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← h1 g, ← h2 g]
    ring
  intro g
  have e := hz _ _ _ h0 g
  rw [Fin.sum_univ_add] at e
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at e
  rw [hΨ g]
  beta_reduce
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination -ζ * e

theorem conjFun_zero (hz : RelConj M κ τ) (ζ : ℂ) : ConjFun M κ τ ζ 0 0 := by
  have e0 : Expands M κ (0 : GA D (Wc D i) → ℂ) (Fin.elim0 : Fin 0 → ℂ) Fin.elim0 := fun g => by simp
  refine ⟨⟨0, _, _, e0⟩, fun n a f e => ?_⟩
  exact expands_conj_swap hz ζ e0 e (fun g => by simp)

theorem conjFun_add (hz : RelConj M κ τ) {ζ : ℂ} {Φ₁ Φ₁' Φ₂ Φ₂' : GA D (Wc D i) → ℂ} (h₁ : ConjFun M κ τ ζ Φ₁ Φ₁')
    (h₂ : ConjFun M κ τ ζ Φ₂ Φ₂') : ConjFun M κ τ ζ (Φ₁ + Φ₂) (Φ₁' + Φ₂') := by
  obtain ⟨⟨n₁, a₁, f₁, e₁⟩, k₁⟩ := h₁
  obtain ⟨⟨n₂, a₂, f₂, e₂⟩, k₂⟩ := h₂
  have e₁₂ : Expands M κ (Φ₁ + Φ₂) (Fin.append a₁ a₂) (Fin.append f₁ f₂) := by
    intro g
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [e₁ g, e₂ g]
  refine ⟨⟨_, _, _, e₁₂⟩, fun n a f e => expands_conj_swap hz ζ e₁₂ e ?_⟩
  intro g
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply]
  rw [k₁ _ _ _ e₁ g, k₂ _ _ _ e₂ g]

theorem conjFun_smul (hz : RelConj M κ τ) {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ} (b : ℂ) (h : ConjFun M κ τ ζ Φ Φ') :
    ConjFun M κ τ ζ (b • Φ) (τ b • Φ') := by
  obtain ⟨⟨n, a, f, e⟩, k⟩ := h
  have eb : Expands M κ (b • Φ) (fun j => b * a j) f := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul, e g, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, eb⟩, fun n' a' f' e' => expands_conj_swap hz ζ eb e' ?_⟩
  intro g
  rw [Pi.smul_apply, smul_eq_mul, k _ _ _ e g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [map_mul]
  ring

end Generic

end GlobalTheory.ConjSpan

namespace GlobalTheory.ConjSpan

section Generic2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ}

theorem conjFun_sum (hz : RelConj M κ τ) (ζ : ℂ) {ι : Type} (Φ Φ' : ι → GA D (Wc D i) → ℂ) :
    ∀ s : Finset ι, (∀ j ∈ s, ConjFun M κ τ ζ (Φ j) (Φ' j)) → ConjFun M κ τ ζ (∑ j ∈ s, Φ j) (∑ j ∈ s, Φ' j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using conjFun_zero hz ζ
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conjFun_add hz (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Generic2

theorem levJ_eq {D : D7} {S T : HSp D} (B : Base S T) (ψ ψ' : Twist D Circle) (h : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  unfold Base.levJ Base.levS
  rw [h]
  rfl

end GlobalTheory.ConjSpan

namespace GlobalTheory.ConjSpan

section Generic3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ}

end Generic3

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {w : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {B : Base (Vc D i) (Wc D i)}
  {W : Type} [AddCommGroup W] [Module ℂ W] (io : W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (c : VsV D i ℂ →ₗ[ℂ] W)

theorem conjVec_smul (z : ℂ) {x0 x1 : VsV D i ℂ} (h : ConjVec i τ x0 x1) : ConjVec i τ (z • x0) (τ z • x1) := by
  unfold ConjVec at h ⊢
  simp only [Submodule.coe_smul]
  rw [h, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  rfl


set_option maxHeartbeats 800000 in
theorem classSum_conj (hz : RelConj M w τ) {p κ ζ : ℂ} (hκ0 : κ ≠ 0) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q)
    {ω ω' : PairRep (Vc D i) (Wc D i)}
    (H : ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun M w τ ζ
      (p • series B.F ω (B.vecFlat ψ) h (io (c x))) (p • series B.F ω' (B.vecFlat ψ') h (io (c x'))))
    (I : Type) [Fintype I] (rep : I → GA D (Vc D i)) (hfin : ∀ j, rep j ∈ GfC (Vc D i))
    (f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank)
    (hff : ∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = io (c x) ∧ f' h = io (c ((τ κ / κ) • x'))) :
    ConjFun M w τ ζ ((p * κ) • B.classSum ω ψ rep f) ((p * κ) • B.classSum ω' ψ' rep f') := by
  rw [B.classSum_apply, B.classSum_apply, Finset.smul_sum, Finset.smul_sum, levJ_eq B ψ ψ' hQ]
  refine conjFun_sum hz ζ _ _ _ fun j _ => ?_
  rw [smul_comm (p * κ), smul_comm (p * κ)]
  obtain ⟨x, x', hxx, hx, hx'⟩ := hff (finPt (Vc D i) (rep j))
  have key : ConjFun M w τ ζ ((p * κ) • series B.F ω (B.vecFlat ψ) (rep j) (f (finPt (Vc D i) (rep j))))
      ((p * κ) • series B.F ω' (B.vecFlat ψ') (rep j) (f' (finPt (Vc D i) (rep j)))) := by
    have e1 : (p * κ) • series B.F ω (B.vecFlat ψ) (rep j) (f (finPt (Vc D i) (rep j))) =
        p • series B.F ω (B.vecFlat ψ) (rep j) (io (c (κ • x))) := by
      rw [hx, map_smul, map_smul, map_smul, smul_smul]
    have e2 : (p * κ) • series B.F ω' (B.vecFlat ψ') (rep j) (f' (finPt (Vc D i) (rep j))) =
        p • series B.F ω' (B.vecFlat ψ') (rep j) (io (c (τ κ • x'))) := by
      rw [hx']
      simp only [map_smul, smul_smul]
      congr 1
      field_simp
    rw [e1, e2]
    exact H (rep j) (hfin j) _ _ (conjVec_smul κ hxx)
  have hr := conjFun_smul hz ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (B.levJ ψ) (finPt (Vc D i) (rep j))) : ℂ)⁻¹) key
  rw [map_inv₀, map_natCast] at hr
  exact hr

end Core

section Core2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  {M : OMDat T.toCore R i Tp tup} {w : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {B : Base (Vc D i) (Wc D i)}
  {W : Type} [AddCommGroup W] [Module ℂ W] (io : W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (c : VsV D i ℂ →ₗ[ℂ] W)
  {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)}

end Core2

end GlobalTheory.ConjSpan
end
end

