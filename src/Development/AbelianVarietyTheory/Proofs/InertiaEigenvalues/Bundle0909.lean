module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaLiftsIsConjugateCuspExpansion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCombine

variable {X B : Type} (φ : B → X → ℂ) (τ : ℂ ≃+* ℂ)

def Exp (Φ : X → ℂ) {n : ℕ} (a : Fin n → ℂ) (F : Fin n → B) : Prop :=
  ∀ g, Φ g = ∑ k, a k * φ (F k) g

def CF (ζ : ℂ) (Φ Φ' : X → ℂ) : Prop :=
  (∃ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F) ∧
    ∀ (n : ℕ) (a : Fin n → ℂ) (F : Fin n → B), Exp φ Φ a F → Exp φ Φ' (fun k => ζ * τ (a k)) F

variable {φ τ}

theorem conj_wd {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {Φ : X → ℂ} {n m : ℕ} {a : Fin n → ℂ} {F : Fin n → B}
    {b : Fin m → ℂ} {G : Fin m → B} (ha : Exp φ Φ a F) (hb : Exp φ Φ b G) (g : X) :
    ∑ k, τ (a k) * φ (F k) g = ∑ k, τ (b k) * φ (G k) g := by
  obtain ⟨p, c, H, hc⟩ := h0.1
  have hall : Exp φ Ψ (Fin.append c (Fin.append a (-b))) (Fin.append H (Fin.append F G)) := by
    intro x
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hc x, ← ha x, ← hb x]
    ring
  have e1 := h0.2 _ _ _ hc g
  have e2 := h0.2 _ _ _ hall g
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at e2
  simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, one_mul, neg_mul,
    Finset.sum_neg_distrib] at e1 e2
  rw [e1] at e2
  linear_combination -e2

theorem conj_comb {Ψ Ψ' : X → ℂ} (h0 : CF φ τ 1 Ψ Ψ') {m : ℕ} (β : Fin m → ℂ) (Φs Φs' : Fin m → X → ℂ)
    (h : ∀ k, CF φ τ 1 (Φs k) (Φs' k)) (c : ℂ) :
    CF φ τ c (fun g => ∑ k, β k * Φs k g) (fun g => c * ∑ k, τ (β k) * Φs' k g) := by
  choose n b G hG using fun k => (h k).1
  let e := (finSigmaFinEquiv (n := n)).symm
  have hflat : Exp φ (fun g => ∑ k, β k * Φs k g) (fun q => β (e q).1 * b (e q).1 (e q).2)
      (fun q => G (e q).1 (e q).2) := by
    intro g
    rw [Fintype.sum_equiv e (fun q => β (e q).1 * b (e q).1 (e q).2 * φ (G (e q).1 (e q).2) g)
      (fun p => β p.1 * b p.1 p.2 * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hG k g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨⟨_, _, _, hflat⟩, fun N a F ha g => ?_⟩
  have hw := conj_wd h0 ha hflat g
  rw [Fintype.sum_equiv e (fun q => τ (β (e q).1 * b (e q).1 (e q).2) * φ (G (e q).1 (e q).2) g)
      (fun p => τ (β p.1 * b p.1 p.2) * φ (G p.1 p.2) g) (fun _ => rfl), Fintype.sum_sigma] at hw
  have hc : ∀ k, Φs' k g = ∑ j, τ (b k j) * φ (G k j) g := fun k => by
    rw [(h k).2 _ _ _ (hG k) g]
    simp only [one_mul]
  show c * ∑ k, τ (β k) * Φs' k g = ∑ k, c * τ (a k) * φ (F k) g
  simp only [hc, map_mul] at hw ⊢
  have e3 : ∑ k, c * τ (a k) * φ (F k) g = c * ∑ k, τ (a k) * φ (F k) g := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [e3, hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ConjCombine

namespace GlobalTheory.ConjClassSum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem conjFun_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ GlobalTheory.ConjCombine.CF (fun (F : T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) g =>
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) (F : T.toCore.R ((i : ℕ) + 1)) g)
      τ ζ Φ Φ' := Iff.rfl

theorem conjFun_congr {Tp Tp' : Type} {tup : Tp → T0} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup)
    (O' : OMDat T.toCore R i Tp' tup') (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) (ζ : ℂ) (Φ Φ' : GA D (Wc D i) → ℂ) :
    ConjFun O κ τ ζ Φ Φ' ↔ ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands
  rw [GlobalTheory.OneMapAll.phi_eq O O' (T.cE ((i : ℕ) + 1))]

def psi {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) : ℂ :=
  T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * M.mu g *
    rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2

theorem psi_smul {Tp : Type} {tup : Tp → T0} (M : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (z : G)
    (u : M.c'.F) (f : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') (g : GA D (Wc D i)) :
    psi M κ z (u • f) g = (u : ℂ) * psi M κ z f g := by
  unfold psi
  rw [map_smul, map_smulₛₗ]
  show _ * ((u : ℂ) * _) = _
  ring


set_option maxHeartbeats 8000000 in
theorem conj_lifts : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hsz hC hT0 hFW hio hQ i hOP hPT c hc τ hτ
  obtain ⟨fw⟩ := hFW
  have hTie : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  obtain ⟨M, hMP, hlev, hext, hnorm, hcurve, hxiF, hcov⟩ :=
    GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hC hT0 ⟨fw⟩ hQ i hOP

  let τQ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => map_ratCast τ q)
  let ta : M.c'.F ≃+* M.c'.F := (τQ.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => τQ.restrictNormal_commutes M.c'.F a

  have hEq0 : (O i).EquivAt (κ i) (T.cE ((i : ℕ) + 1) (O i).s0) :=
    (hPT (_root_.GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie hio O i hOP)).1
  have hlev2 : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hEqM : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt at hEq0 ⊢
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), hlev2]
    exact hEq0
  have hcM : ExtC R i (inC M.c') M.c0' c := (hext c).1 hc

  obtain ⟨ζ, z, hζ, -, hser⟩ := _root_.GlobalTheory.SerAll.ser_at_core_constants hCI D G Pl0 T0 A T R F κ v₀ O ph hsz hC hT0 ⟨fw⟩ hio hQ i hOP hPT T0 id M hMP
    hlev hext
  obtain ⟨hf, k0, hk0, hgal⟩ := _root_.GlobalTheory.GalEqCls.galRul_isSum hCI D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hcurve hxiF
  obtain ⟨a0, ha0, hza⟩ := hζ
  obtain ⟨b0, hb0, hkb⟩ := hk0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha0.ne'] at hza
    exact zero_ne_one hza
  have hτζ : τ ζ ≠ 0 := (map_ne_zero τ).2 hζ0
  refine ⟨ζ * k0 / τ ζ, ⟨a0 * b0, Nat.mul_pos ha0 hb0, ?_⟩, fun t t' hct => ?_⟩
  · rw [div_pow, mul_pow, ← map_pow, pow_mul ζ a0 b0, hza, one_pow, pow_mul' k0 a0 b0, hkb, one_pow, map_one, div_one,
      one_mul]
  obtain ⟨e, hsame⟩ := hcov t t' hct.1
  obtain ⟨u, s, hu, hgal'⟩ := hgal t t' e hsame hct
  refine ⟨s, fun y y' hcf => ?_⟩
  obtain ⟨n, α, ys, ys', hy, hy', hval⟩ :=
    _root_.GlobalTheory.ConjDesc.conj_desc D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ c hcM hxiF t t' hct y y' hcf
  obtain ⟨h, J', hR, -⟩ := (hMP.tuple t).reps
  have hlevJ := ((_root_.GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct).2.2.2 i hτ).1
  have hR' : RepsR R i t' (fun j => h (e.symm j)) (M.bad t') J' (M.Lh t') (M.gam t') (M.vol t') := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hR
    obtain ⟨-, -, -, hbad, hvol, hk⟩ := hsame
    have hQ' : R.Q t' = R.Q t := hct.1
    refine ⟨hbad ▸ h1, fun PP hPP => ?_, ?_, ?_, ?_, fun g => ?_, fun j => ?_⟩
    · rw [hbad]; exact h2 PP (hQ' ▸ hPP)
    · rw [hlevJ]; exact h3
    · rw [hlevJ]; exact h4
    · rw [hlevJ, hvol]; exact h5
    · obtain ⟨p, hp, huniq⟩ := h6 g
      refine ⟨e p, by simpa using hp, fun j hj => ?_⟩
      have := huniq (e.symm j) hj
      rw [← this]
      simp
    · obtain ⟨a1, a2, a3⟩ := h7 (e.symm j)
      have hkj := hk (e.symm j)
      simp only [Equiv.apply_symm_apply] at hkj
      exact ⟨hbad ▸ a1, hkj.1.trans a2, hkj.2.2.2.trans a3⟩

  choose xv xv' hxv using hval
  let xs : Fin n → M.Cl' t → VsV D i M.c'.F := fun k p => xv k (h p)
  let xs' : Fin n → M.Cl' t' → VsV D i M.c'.F := fun k j => xv' k (h (e.symm j))
  choose f hfc hfs using fun k => GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hCI D G Pl0 T0 A T R F κ v₀ hC hTie i T0 id M
    hMP t (xs k)
  have hsec : ∀ k, f k ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := fun k =>
    cusp_le_sec _ _ _ _ _ (hfc k)
  have hA : ∀ k g, ph i * R.thF i t (ys k) (v₀ i (sg0 D A)) g = ζ * psi M (κ i) z (f k) g := fun k g => by
    refine (hser t h J' hR (ys k) (xs k) (fun p => (hxv k (h p)).2.1) (f k) (hsec k) (hfs k) g).trans ?_
    unfold psi
    ring
  have hG : ∀ k, u • galRul hf (f k) ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧
      GlobalTheory.OneMapAll.IsSum M t' (xs' k) (u • galRul hf (f k)) := fun k =>
    hgal' (xs k) (xs' k) (fun p => by simp only [xs, xs', Equiv.symm_apply_apply]; exact (hxv k (h p)).1) (f k) (hsec k)
      (hfs k)
  have hB : ∀ k g, ph i * R.thF i t' (ys' k) (v₀ i (sg0 D A)) g = ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g :=
    fun k g => by
    refine (hser t' (fun j => h (e.symm j)) J' hR' (ys' k) (xs' k) (fun j => (hxv k (h (e.symm j))).2.2)
      (u • galRul hf (f k)) (hG k).1 (hG k).2 g).trans ?_
    rw [show ζ * (u : ℂ) * psi M (κ i) z (galRul hf (f k)) g = ζ * ((u : ℂ) * psi M (κ i) z (galRul hf (f k)) g) by ring,
      ← psi_smul]
    unfold psi
    ring
  have hbc : ∀ k, ConjFun M (κ i) τ 1 (psi M (κ i) z (f k)) (psi M (κ i) z (galRul hf (f k))) := fun k =>
    _root_.GlobalTheory.ConjExpand.conjFun_galRul D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z (f k) (hfc k) hEqM
  have hbc0 : ConjFun M (κ i) τ 1 (psi M (κ i) z 0) (psi M (κ i) z (galRul hf 0)) :=
    _root_.GlobalTheory.ConjExpand.conjFun_galRul D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP τ ta hta hτ hf z 0 (Submodule.zero_mem _) hEqM
  have hcomb := GlobalTheory.ConjCombine.conj_comb ((conjFun_iff M (κ i) τ 1 _ _).1 hbc0) (fun k => ζ * α k)
    (fun k => psi M (κ i) z (f k)) (fun k => psi M (κ i) z (galRul hf (f k)))
    (fun k => (conjFun_iff M (κ i) τ 1 _ _).1 (hbc k)) (ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ))
  have hΦ : (fun g => ph i * R.thF i t y (v₀ i (sg0 D A)) g) =
      fun g => ∑ k, (ζ * α k) * psi M (κ i) z (f k) g := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, hA k g]
    ring
  have hΦ' : (fun g => ph i * R.thF i t' y' (v₀ i (sg0 D A)) g) =
      fun g => ζ * k0 / τ ζ * ((R.xi t' s : Circle) : ℂ) * ∑ k, τ (ζ * α k) * psi M (κ i) z (galRul hf (f k)) g := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy', map_sum]
    simp only [map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hu' : (u : ℂ) = k0 * ((R.xi t' s : Circle) : ℂ) := hu
    have hcan : ζ * k0 / τ ζ * τ ζ = ζ * k0 := div_mul_cancel₀ _ hτζ
    rw [mul_left_comm, hB k g, hu', map_mul]
    linear_combination (-(τ (α k) * ((R.xi t' s : Circle) : ℂ) * psi M (κ i) z (galRul hf (f k)) g)) * hcan
  rw [conjFun_congr (O i) M, conjFun_iff, hΦ, hΦ']
  exact hcomb

end GlobalTheory.ConjClassSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Topology
open Filter

namespace GlobalTheory.LatFixMod

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem eventually_keep_cong (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1,
      (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T p.1 p.2 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T p.1 p.2 u = u + N • l := by
  set L := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) with hLdef
  have hfg := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  obtain ⟨G, hG, hGl, hgen⟩ := hfg
  have hev := GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  have hall := (Filter.eventually_all_finite hG).2 fun u hu =>
    hev.2 u (GlobalTheory.SplitScalar.latO_fin (hGl u hu)) N hN
  filter_upwards [hev.1, hall] with p hk hp
  refine ⟨hk, fun w hw => ?_⟩
  let U : AddSubgroup (WO S T) :=
    { carrier := {w | ∃ l ∈ L, actO S T p.1 p.2 w = w + N • l}
      zero_mem' := ⟨0, L.zero_mem, by
        have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
        rw [zero_smul, zero_smul] at this
        rw [this, smul_zero, add_zero]⟩
      add_mem' := by
        rintro a b ⟨la, hla, ea⟩ ⟨lb, hlb, eb⟩
        refine ⟨la + lb, L.add_mem hla hlb, ?_⟩
        rw [GlobalTheory.LatNhds.actO_add, ea, eb, smul_add]
        abel
      neg_mem' := by
        rintro a ⟨la, hla, ea⟩
        refine ⟨-la, L.neg_mem hla, ?_⟩
        have h0 := GlobalTheory.LatNhds.actO_add p.1 p.2 a (-a)
        have hz : actO S T p.1 p.2 (0 : WO S T) = 0 := by
          have := GlobalTheory.LatNhds.actO_smul p.1 p.2 (0 : AE D) (0 : WO S T)
          rw [zero_smul, zero_smul] at this
          rw [this]
        rw [add_neg_cancel, hz, ea] at h0
        rw [smul_neg]
        have : actO S T p.1 p.2 (-a) = -(a + N • la) := (neg_eq_of_add_eq_zero_right h0.symm).symm
        rw [this, neg_add] }
  refine hgen U (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
  show actO S T p.1 p.2 _ = _
  rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, smul_comm]

def KeepMod (S T : HSp D) (L : AddSubgroup (WO S T)) (N : ℕ) (x : GA D S) : Prop :=
  (∀ u ∈ L, actO S T x 1 u ∈ L) ∧ ∀ u ∈ L, ∃ l ∈ L, actO S T x 1 u = u + N • l

theorem exists_open_keep_cong : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N →
    ∃ J : Subgroup (Bridge.Gf S), IsOpen (J : Set (Bridge.Gf S)) ∧ ∀ x ∈ GfC S, fin S x ∈ J →
      (∀ u : WO S T, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
        actO S T x 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∃ l ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          actO S T x 1 u = u + N • l := by
  intro D S T ΛS ΛT hS hT N hN
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hev := eventually_keep_cong S T ΛS ΛT hS hT N hN
  have t1 : Tendsto (fun x : GA D S => ((x, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_id.prodMk continuous_const : Continuous fun x : GA D S => ((x, (1 : GA D T))))).tendsto 1
    exact this
  have t2 : Tendsto (fun x : GA D S => ((x⁻¹, 1) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_inv.prodMk continuous_const : Continuous fun x : GA D S => ((x⁻¹, (1 : GA D T))))).tendsto 1
    rwa [inv_one, Prod.mk_one_one] at this
  have hx : ∀ᶠ x in 𝓝 (1 : GA D S),
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N x⁻¹ :=
    (t1.eventually hev).and (t2.eventually hev)
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial k →
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
      KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹ := by
    by_contra hne
    have hne' : ∀ n : ℕ, ∃ k, k ∈ GfC S ∧ GlobalTheory.Member.FinCong S n.factorial k ∧
        ¬ (KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k ∧
          KeepMod S T (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) N k⁻¹) :=
      fun n => by
        by_contra h
        exact hne ⟨n, fun k hk hc => by
          by_contra h'
          exact h ⟨k, hk, hc, h'⟩⟩
    choose k hk hkc hkne using hne'
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hx).exists
    exact hkne n hn
  obtain ⟨n, hn⟩ := key
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup S n.factorial).map (finHom S).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup S n.factorial_pos, fun x hxf hJ => ?_⟩
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hJ
  have e' : finHom S k' = finHom S x := congrArg Subtype.val e
  have hc : GlobalTheory.Member.FinCong S n.factorial x := by
    have := hk'.2
    unfold GlobalTheory.Member.FinCong at this ⊢
    rw [← e']
    exact this
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hn x hxf hc
  refine ⟨fun u => ⟨h1 u, fun hu => ?_⟩, h2⟩
  have e2 := GlobalTheory.WeilVacMove.actO_inv_actO x (1 : GA D T) u
  rw [inv_one] at e2
  rw [← e2]
  exact h3 _ hu

end GlobalTheory.LatFixMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option autoImplicit false

namespace GlobalTheory.ConjRefLift

section Scale

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {c : ℂ} (hc : c ≠ 0)
    {Ψ Ψ' Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ 1 Ψ Ψ') (e : ∀ g, Φ g = c⁻¹ * Ψ g)
    (e' : ∀ g, Φ' g = (τ c)⁻¹ * Ψ' g) : ConjFun O κ τ 1 Φ Φ' := by
  obtain ⟨⟨n, a, f, ha⟩, hall⟩ := h
  have hτc : τ c ≠ 0 := (map_ne_zero τ).2 hc
  refine ⟨⟨n, fun k => c⁻¹ * a k, f, fun g => ?_⟩, fun m b f' hb g => ?_⟩
  · rw [e g, ha g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hb' : Expands O κ Ψ (fun k => c * b k) f' := fun g => by
      have h1 := hb g
      rw [e g] at h1
      have h2 : Ψ g = c * (c⁻¹ * Ψ g) := by field_simp
      rw [h2, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e' g, hall m _ f' hb' g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, one_mul]
    field_simp

theorem conjFun_congr {Tp' : Type} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup) (O' : OMDat T.toCore R i Tp' tup')
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ}
    (hphi : O.phi (T.cE ((i : ℕ) + 1) O.s0) = O'.phi (T.cE ((i : ℕ) + 1) O'.s0)) (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands at h ⊢
  rw [← hphi]
  exact h

end Scale


set_option maxHeartbeats 2000000 in
theorem conjFun_lifts_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs c₀ hc₀ hc₀P
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := _root_.GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hC D G Pl0 T0 A T R F κ v₀ hcore hT hio O i hpins
  have hEqO := (hphase hrow0).1
  have elev : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hMl]
  have hEq : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), elev]
    exact hEqO
  obtain ⟨ζ, z, hζ, -, hser⟩ :=
    _root_.GlobalTheory.SerAll.ser_at_core_constants hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin ⟨fw⟩ hio hQ i hpins hphase T0 id M hMp hMl hMe
  obtain ⟨nζ, hnζ, hζn⟩ := hζ
  obtain ⟨nc, hnc, hcn⟩ := hc₀
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0, hnζ.ne'] at hζn
  have hc0 : ((c₀ : M.c'.F) : ℂ) ≠ 0 := fun h0 => by simp [h0, hnc.ne'] at hcn
  refine ⟨(ζ * (c₀ : ℂ))⁻¹, ⟨nζ * nc, Nat.mul_pos hnζ hnc, ?_⟩, fun τ ta hta hB y y' hyy => ?_⟩
  · rw [inv_pow, mul_pow, pow_mul, hζn, one_pow, mul_comm nζ nc, pow_mul, hcn, one_pow, mul_one, inv_one]
  have hf : Fixes M.c' ta :=
    fixes_of_le (c := T.Q.c) ta fun x hx => Subtype.ext ((hta x).trans (hB.core ⟨x, hx⟩))
  obtain ⟨h, J', hR, -⟩ := (hMp.tuple A.μ0).reps
  choose x x' hxx hx hx' using fun k => hyy (h k)
  have hio' : ∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k)) := fun k =>
    _root_.GlobalTheory.IoConj.io_map_conj D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB (x k) (x' k) (hxx k)
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hC D G Pl0 T0 A T R F κ v₀ hcore hT i T0 id M hMp A.μ0 x
  obtain ⟨f, hf2⟩ := hex
  have hfc := hf2.1
  have hfs := hf2.2
  have hfsec : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hP' := hc₀P τ ta hta hB hf x x' hio' f hfsec hfs
  have e1 := hser A.μ0 h J' hR y x hx f hfsec hfs
  have e2 := hser A.μ0 h J' hR y' x' hx' _ hP'.1 hP'.2
  dsimp only [id_eq] at e1 e2
  have hCM := _root_.GlobalTheory.ConjExpand.conjFun_galRul D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB hf z f hfc hEq
  have hsm : ∀ (s : M.c'.F) (Fr : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') a b,
      rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (s • Fr)) a b =
        inC M.c' s * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z Fr) a b := by
    intro s Fr a b
    rw [map_smul, map_smulₛₗ]
    rfl
  have hcv : inC M.c' c₀ = (c₀ : ℂ) := rfl
  have htv : inC M.c' (ta c₀) = τ (c₀ : ℂ) := hta c₀
  have hτ0 : τ (c₀ : ℂ) ≠ 0 := (map_ne_zero τ).2 hc0
  refine conjFun_scale (O i) (κ i) τ hc0 (conjFun_congr M (O i) (GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1))) hCM)
    (fun g => ?_) (fun g => ?_)
  · beta_reduce
    rw [mul_assoc, e1 g]
    field_simp
  · beta_reduce
    have hs := hsm ((ta c₀ * c₀⁻¹)⁻¹) (galRul hf f) (M.dict g).1 (M.dict g).2
    rw [mul_assoc, e2 g]
    erw [hs]
    rw [map_inv₀, map_mul, map_inv₀, hcv, htv]
    field_simp

end GlobalTheory.ConjRefLift
end

