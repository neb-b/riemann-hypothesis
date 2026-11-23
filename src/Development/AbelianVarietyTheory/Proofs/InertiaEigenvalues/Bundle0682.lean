module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCommutationRealExpansion
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.Unique

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_congr (rc rc' : IrrGL (k := w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E)))
    (H : ∀ Δ ∈ l, rc Δ.first = rc' Δ.first) : segSum rc l = segSum rc' l := by
  unfold segSum
  congr 1
  exact List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]

theorem first_fst_le_of_isL {k V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {𝔪 : Multiset (Segment k)}
    (hL : IsL 𝔪 π) {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : Δ.first.1 ≤ N := by
  obtain ⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩ := hL
  rw [← hmap] at hΔ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have h1 := (hLs i).deg_eq
  have h2 : (xs i).1 ≤ ∑ a, (xs a).1 := Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (Δs i).d ≤ (Δs i).deg := Nat.le_mul_of_pos_left _ (Δs i).len_pos
  show (Δs i).d ≤ N
  omega

theorem eq_of_isCusp (hLC : LocalConverseGL) (hBZ : BernsteinZelevinskyFiniteness)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc rc' : IrrGL (k := w.adicCompletion E) → WD h}
    {ψ : AddChar (w.adicCompletion E) Circle} (hψc : Continuous ψ) (hψ : ψ ≠ 1) (he : e ψ = e' ψ)
    (H : LawsMin a ha e rc) (H' : LawsMin a ha e' rc') (x : IrrGL (k := w.adicCompletion E)) (hx : x.IsCusp)
    (ih : ∀ y : IrrGL (k := w.adicCompletion E), y.1 < x.1 → rc y = rc' y) : rc x = rc' x := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨n, c⟩ := x
  obtain ⟨hn, hc⟩ := hx
  rcases n with _ | m
  · exact absurd hn (lt_irrefl 0)
  rcases m with _ | m
  · obtain ⟨χ, hχ, hx⟩ := GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl
    rw [hx, H.one, H'.one]
  · obtain ⟨x', hx'⟩ := H'.bij.2 (rc ⟨m + 2, c⟩)
    have hd : x'.1 = m + 2 := by
      have := H'.dim x'
      rw [hx', H.dim] at this
      exact this.symm
    have hcx' : x'.IsCusp := (H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)
    obtain ⟨n', c'⟩ := x'
    obtain rfl : n' = m + 2 := hd
    have hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩ := fun d => by
      simp [cls, IrrCl.cl_rep]
    have key : c = c' := by
      rw [← c.cl_rep, ← c'.cl_rep]
      refine IrrRep.cl_eq_iff.2 ?_
      refine hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_
      have h2 : rc (cls τ) = rc' (cls τ) := ih _ (by show m + 1 < m + 2; omega)
      refine ⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩
      have h1 := H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2
      rw [hcls] at h1 ⊢
      rw [he, ← hx', h2]
      exact h1
    subst key
    exact hx'.symm

theorem eq_of_lawsMin : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  intro hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have main : ∀ n, ∀ x : IrrGL (k := w.adicCompletion E), x.1 = n → rc x = rc' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      obtain ⟨𝔪, h𝔪⟩ := hEx _ x
      have hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
      rw [H.langlands _ x hL, H'.langlands _ x hL]
      refine segSum_congr rc rc' _ fun Δ hΔ => ?_
      have hle : Δ.first.1 ≤ n := hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)
      exact eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first
        fun y hy => ih y.1 (by omega) y rfl
  funext x
  exact main _ x rfl

end GlobalTheory.LocLanglands.Unique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCompSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

theorem aeval_intertwine {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (e : M ≃ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, e (A x) = B (e x)) (p : K[X]) (x : M) :
    e (Polynomial.aeval A p x) = Polynomial.aeval B p (e x) := by
  have hpow : ∀ n : ℕ, ∀ x, e ((A ^ n) x) = (B ^ n) (e x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a => simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]

theorem separable_comp_smul {K : Type} [Field K] {p : K[X]} (hp : p.Separable) {a : K} (ha : a ≠ 0) :
    (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (Polynomial.C a * Polynomial.X))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (Polynomial.C a * Polynomial.X)) (Polynomial.C a) :=
    ⟨0, Polynomial.C a⁻¹, by rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]⟩
  have h3 : Polynomial.derivative (p.comp (Polynomial.C a * Polynomial.X)) =
      (Polynomial.derivative p).comp (Polynomial.C a * Polynomial.X) * Polynomial.C a := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, mul_one, mul_comm]
  show IsCoprime _ _
  rw [h3]
  exact h1.mul_right h2

theorem aeval_smul_comp {K M : Type} [Field K] [AddCommGroup M] [Module K M] (B : Module.End K M) {c : K}
    (hc : c ≠ 0) (p : K[X]) (y : M) :
    Polynomial.aeval (c • B) (p.comp (Polynomial.C c⁻¹ * Polynomial.X)) y = Polynomial.aeval B p y := by
  rw [Polynomial.aeval_comp]
  congr 2
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, inv_mul_cancel₀ hc, one_smul]


set_option maxHeartbeats 800000 in
theorem hkF_separable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y) : CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
      ∃ p : (FractionRing (D.ntw.O i))[X], p.Separable ∧
        ∀ x ∈ V0 D.nexp i j b, Polynomial.aeval (D.nexp.hkF i j b k P) p x = 0 := by
  intro hG hC hX hR hU hI hS0c hS02 hS0b i hi j hj b k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨q, hqs, hq⟩ := _root_.GlobalTheory.GoodSS.Heart.hL_separable_good Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk

  set rd : ↥D.LL0 →+* KB S i b := readLL0 S i b with hrd
  set hst := Y.rho j h1 h2
  set hχ := Y.chi j h1 h2
  set T0 := GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) with hT0
  set s := (D.nexp.eAlg i b).coeff.support with hs
  set a : G0g D.nd → ↥D.LL0 := fun g => D.nexp.eLL0 g * (chiL S j hχ (S.eG.symm g))⁻¹ with ha
  set ρ : G0g D.nd → Module.End S.Ks (FmK S j) := fun g => rhoKG S j hst (S.eG.symm g) with hρ

  have hcoef : ∀ g, (D.nexp.eAlg i b).coeff g = rd (D.nexp.eLL0 g) := fun g => by
    rw [D.nexp.eAlg_def]; rfl
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    rw [hcoef] at h0
    exact (map_eq_zero_iff rd rd.injective).1 h0

  have hE' : GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j hst hχ D.nexp.eLL0 = ∑ g ∈ s, a g • LinearMap.baseChange ↥D.LL0 (ρ g) := by
    unfold GlobalTheory.GoodSS.goodProjectorBaseChangeForms
    refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
    by_contra hgs
    exact hg (by simp only [hsupp g hgs, zero_mul, zero_smul])

  have hdesc := GlobalTheory.T.baseChange_polynomial_annihilates_descent S.Ks ↥D.LL0 (KB S i b) (FmK S j) (G0g D.nd) rd (fun _ => rfl) T0 s ρ a q
    (fun z hz => hq z (hE' ▸ hz))
  set c := H.cHk i b k P with hc
  have hc0 : c ≠ 0 := by
    rw [hc, H.cHk_pow]
    exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero

  set B : Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) := LinearMap.baseChange (KB S i b) T0 with hB
  have hAB : ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = (c • B) (Y.eF i j b h1 h2 x) := fun x =>
    H.hkEq i j b h1 h2 k P x hk.2.2.2 hk.2.2.1 hk.2.1

  have hE : ∀ x0, Y.eF i j b h1 h2 (eG D.nexp i j b x0) =
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange (KB S i b) (ρ g)) (Y.eF i j b h1 h2 x0) := by
    intro x0
    have hact : ∀ g y, actG S i j b hst hχ g y =
        (rd (chiL S j hχ (S.eG.symm g)))⁻¹ • LinearMap.baseChange (KB S i b) (ρ g) y := fun _ _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eG, MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine (Finset.sum_congr rfl fun g _ => ?_).trans (LinearMap.sum_apply _ _ _).symm
    change Y.eF i j b h1 h2 ((D.nexp.eAlg i b).coeff g • D.nexp.actG i j b g x0) =
      rd (a g) • LinearMap.baseChange (KB S i b) (ρ g) (Y.eF i j b h1 h2 x0)
    rw [map_smul, Y.act i j b h1 h2 g x0, hact, hcoef]
    have hag : rd (a g) = rd (D.nexp.eLL0 g) * (rd (chiL S j hχ (S.eG.symm g)))⁻¹ := by
      simp only [ha, map_mul, map_inv₀]
    rw [hag]
    exact (mul_smul _ _ _).symm
  refine ⟨(q.map rd).comp (Polynomial.C c⁻¹ * Polynomial.X), ?_, ?_⟩
  · exact separable_comp_smul ((Polynomial.separable_map rd).2 hqs) (inv_ne_zero hc0)
  · rintro x ⟨x0, -, rfl⟩
    apply (Y.eF i j b h1 h2).injective
    rw [map_zero]
    refine (aeval_intertwine (Y.eF i j b h1 h2) _ (c • B) hAB _ _).trans ?_
    refine (aeval_smul_comp B hc0 _ _).trans ?_
    rw [hE]
    exact hdesc _ ⟨_, rfl⟩

end GlobalTheory.GoodSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm


set_option maxHeartbeats 3200000 in
theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := _root_.GlobalTheory.sideReal_ofPres (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (_root_.GlobalTheory.HLatLevel.hLat_mul_lev D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.SplitIntLift

theorem exists_lift {R K O : Type} [CommRing R] [CommRing K] [CommRing O] {n : ℕ} (S : Subring R) (π : R →+* K)
    (ι : O →+* K) (p : S) (hinj : ∀ x, π x = 0 → (p : R) * x = 0) (hl : ∀ o, ∃ s : S, π s = ι o)
    (h : GL (Fin n) O) (β g : GL (Fin n) R)
    (hg : (Matrix.GeneralLinearGroup.map π β)⁻¹ * Matrix.GeneralLinearGroup.map π g * Matrix.GeneralLinearGroup.map π β =
      Matrix.GeneralLinearGroup.map ι h) :
    ∃ (Y : Matrix (Fin n) (Fin n) S) (u : S), (∀ i j, π (Y i j) = ι (h.1 i j)) ∧ u * Y.det = p ∧
      (p : R) • g.1 = (p : R) • (β.1 * Y.map S.subtype * (β⁻¹).1) := by
  choose Y hY using fun i j => hl (h.1 i j)
  obtain ⟨u, hu⟩ := hl (h⁻¹).1.det
  have eY : (Matrix.of Y).map (π.comp S.subtype) = h.1.map ι := Matrix.ext hY
  refine ⟨Matrix.of Y, p * u, hY, Subtype.ext ?_, ?_⟩
  · have e1 : π ((Matrix.of Y).det : S) = ι h.1.det := by
      rw [RingHom.map_det ι, RingHom.mapMatrix_apply, ← eY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    have := hinj (u * ((Matrix.of Y).det : S) - 1) (by
      rw [map_sub, map_mul, hu, e1, ← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one, map_one, sub_self])
    push_cast
    linear_combination this
  · have e2 : Matrix.GeneralLinearGroup.map π g = Matrix.GeneralLinearGroup.map π β * Matrix.GeneralLinearGroup.map ι h *
        Matrix.GeneralLinearGroup.map π β⁻¹ := by
      rw [← hg, map_inv]; group
    have e3 : g.1.map π = (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1).map π := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
      exact (congrArg Units.val e2).trans (congrArg (fun z => β.1.map π * z * (β⁻¹).1.map π) eY.symm)
    ext i j
    have := hinj (g.1 i j - (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1) i j) (by
      rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e3 i) j)
    rw [mul_sub, sub_eq_zero] at this
    exact this

open GlobalTheory.LevSplit GlobalTheory.ParahoricLift Formalism.L2.NTheta GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7}

theorem rdE_finSw {v : FinPl D} (φ : SplitProj D v) (a : Formalism.L2.Theta.AE D) : rdE φ (finSw D a) = rdA φ a :=
  GlobalTheory.SplitProjChart.rdE_toEAf φ a

theorem finSw_surjective (z : Formalism.IndefR.Lev.EAf D) : ∃ w, finSw D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from (0, a)) ⊗ₜ x, rfl⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, RingHom.map_add _ _ _⟩

theorem cut_inj {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e)
    (x : Formalism.IndefR.Lev.EAf D) (hx : rdE φ x = 0) : finSw D e * x = 0 := by
  obtain ⟨w, rfl⟩ := finSw_surjective x
  rw [rdE_finSw] at hx
  rw [← RingHom.map_mul, ((GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.2.1 w).1 hx, RingHom.map_zero]

theorem int_lift {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e) (o : OI v) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, rdE φ s = algebraMap (OI v) (Fv D.host.F v) o := by
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  obtain ⟨a, ha⟩ := h1 (algebraMap (OI v) (Fv D.host.F v) o)
  refine ⟨⟨finSw D (e * a), swapAE_int ((h4 a).2 ⟨o, ha.symm⟩)⟩, ?_⟩
  show rdE φ (finSw D (e * a)) = _
  rw [rdE_finSw, RingHom.map_mul, he.2.2, one_mul, ha]


set_option maxHeartbeats 1000000 in
theorem lift_of_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  intro D V β Λ N hB P v φ e hP0 he0 red hred h κ hs hκ0
  have he : IsIdemAt e P := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ P hP0).2.2 e he0).1
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  have hg : (Matrix.GeneralLinearGroup.map (rdE φ) β)⁻¹ * Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) *
      Matrix.GeneralLinearGroup.map (rdE φ) β = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h := by
    rw [← hκ0]
    have : Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) =
        Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
      Units.ext (Matrix.ext fun i j => rdE_finSw φ (Formalism.L2.Theta.mt V κ i j))
    rw [this]
    rfl
  obtain ⟨Y, u, hY, hu', hκ⟩ := exists_lift (Formalism.L2.Herm.intAf D.host.F D.host.E) (rdE φ)
    (algebraMap (OI v) (Fv D.host.F v)) p (fun x hx => hp ▸ cut_inj he0 x hx) (int_lift he0) h β (finE V κ) hg
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨(T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ]
    refine Matrix.ext fun i j => ?_
    obtain ⟨hi, hr⟩ := hred (Y i j) (Y i j).2
    exact hr.symm.trans (congrArg red (Subtype.ext (hY i j)))
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

end GlobalTheory.DownLift.SplitIntLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_keeps_cuspidal_twists_characters : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  first | exact @GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | exact GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | (intros; apply GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar <;> assumption)
end

