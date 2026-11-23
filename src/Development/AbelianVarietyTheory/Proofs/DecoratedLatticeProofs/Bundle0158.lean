module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
section
noncomputable section

namespace GlobalTheory.Core.Rk.BdSplit

section Abstract

open Formalism.UG GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}


open Classical in
def cosetInd (S : Finset (G ⧸ K)) : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0

theorem cosetInd_mem {S : Finset (G ⧸ K)} (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) : cosetInd S ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, S.image Quotient.out, fun g hg => ?_⟩
  · have e : ((a * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := QuotientGroup.mk_mul_of_mem _ b.2
    have : (a : G) • (g : G ⧸ K) ∈ S ↔ (g : G ⧸ K) ∈ S :=
      ⟨fun h => by simpa using hS _ (inv_mem a.2) _ h, hS _ a.2 _⟩
    simp only [cosetInd, e, this]
  · have h : (g : G ⧸ K) ∈ S := by
      by_contra h
      exact hg (if_neg h)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ h, 1, k⁻¹, by rw [hk]; simp⟩

theorem heckeVec_cosetInd (ρ : Representation ℂ G V) (S : Finset (G ⧸ K)) (x : V) :
    heckeVec ρ K (cosetInd S) x = ∑ c ∈ S, ρ c.out x := by
  rw [heckeVec, finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun c hc => by simp [cosetInd, hc]
  · intro c hc
    by_contra h
    exact hc (by simp [cosetInd, show c ∉ S from h])

theorem norm_le_card {ι : Type} (ρ : Representation ℂ G V) {x : V} (l : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) (S : Finset ι) (g : ι → G) (a : ℂ)
    (h : ∑ c ∈ S, ρ (g c) x = a • x) : ‖a‖ ≤ S.card := by
  have hb : BddAbove (Set.range fun y => ‖l (ρ y x)‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  set M := ⨆ y, ‖l (ρ y x)‖
  have hM : ∀ y, ‖l (ρ y x)‖ ≤ M := fun y => le_ciSup hb y
  have hM0 : 0 < M := (norm_pos_iff.2 h1).trans_le (hM 1)
  have key : ∀ y, ‖a‖ * ‖l (ρ y x)‖ ≤ S.card * M := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← norm_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← h, map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact hM _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : M ≤ S.card * M / ‖a‖ := ciSup_le fun y => by rw [le_div_iff₀' h0]; exact key y
    rw [le_div_iff₀' h0] at this
    exact le_of_mul_le_mul_right this hM0

end Abstract

section Linear

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SatakeBound

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem norm_le_of_isSatVecGL {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (l : V →ₗ[ℂ] ℂ) {C : ℝ} (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) :
    ∀ β ∈ B, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at hφ1
  have hy := isSatVecGL_of_isSpherical hφ hφ0
  have hKO : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  have hb : HasBoundedSums (w.adicCompletion E) φ := by
    intro S hS
    have H := SatCompare.exists_eigenvalue_GL hx hy
    rw [← hKO] at H
    obtain ⟨c, e1, e2⟩ := H _ (cosetInd_mem hS)
    rw [heckeVec_cosetInd] at e1 e2
    have e3 : ∑ c ∈ S, φ c.out = c := by
      have := congrFun e2 1
      rw [Finset.sum_apply, Pi.smul_apply, hφ1, smul_eq_mul, mul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => congrArg φ (one_mul _).symm
    rw [e3]
    exact norm_le_card ρ l hC h1 S _ c e1
  have hs : IsBorelSph (w.adicCompletion E) (fun i : Fin n => (α i : ℂ) *
      (((resCard (w.adicCompletion E) : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ := by
    refine ⟨fun g k hk => congrFun (GlobalTheory.LGrp.mem_fixed.1 hy.2.1 k (hKO ▸ hk)) g, fun b hb' t ht => ?_⟩
    obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n α φ).1 hφ
    have h := GlobalTheory.SatakeBound.Rep.law α y b hb' t ht 1
    rwa [hφ1, mul_one, mul_one] at h
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
  have hq : (0 : ℝ) < resCard (w.adicCompletion E) := by
    exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard (w.adicCompletion E)).le
  have h2 := norm_le_pow hs hb i
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), ← Real.rpow_natCast] at h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h2
  rw [← GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  exact h2.trans_eq (congrArg _ (by ring))

end Linear

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem paramBound_split : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  rintro D A L - v hv par c ⟨⟨C, hC⟩, V, _, _, ρ, x, l, hx, -, hc⟩ h1 w h
  refine ⟨(hx w h).card, fun β hβ => ?_⟩
  rcases hx w h with ⟨-, e, -, hx⟩ | ⟨hw, -⟩
  · have hb := norm_le_of_isSatVecGL hx l (C := C) (fun y => (hc (e.symm y)) ▸ hC (e.symm y))
      (by rw [hc] at h1; rwa [map_one, ← map_one ρ]) β hβ
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm w).le
  · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)

end GlobalTheory.Core.Rk.BdSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotL

theorem e_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.e := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩ := fun a h => by
    have g1 := P.gap_eb ⟨a, by omega⟩ h
    have g2 := P.gap_be ⟨a + 1, h⟩
    linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction d with
  | zero => exact step a hb
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := step (a + d + 1) (by omega)
    have e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1]
    exact h1.trans h2

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.μ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  exact (h η hη a).trans (pow_zero _)

theorem isHecke {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) : IsHeckeChar D (c.μ k) :=
  (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  intro D c hc i j hi hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega))
    (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w := fun w hw =>
      (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.ChainOnto.QuotL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjVal

variable {D : D7}

def Good (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g

theorem Good.add {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f f' : GA D V → ℂ}
    (h : Good V J χ f) (h' : Good V J χ f') : Good V J χ (f + f') := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  obtain ⟨c', ⟨C', hC'⟩, l', r'⟩ := h'
  refine ⟨c.add c', ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩,
    fun γ hγ g => by simp [l γ hγ g, l' γ hγ g], fun k hk g => by simp [r k hk g, r' k hk g, mul_add]⟩

theorem Good.smul {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f : GA D V → ℂ} (a : ℂ)
    (h : Good V J χ f) : Good V J χ (a • f) := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  refine ⟨continuous_const.mul c, ⟨‖a‖ * C, fun g => ?_⟩,
    fun γ hγ g => by simp [l γ hγ g], fun k hk g => by simp [r k hk g, mul_left_comm]⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)

theorem good_val (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    (u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : ⨂[ℂ] τ, M.sm τ) :
    Good V J χ (u v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT θ M J χ u).1 hu)
  have hu' : u = PiTensorProduct.lift (PiTensorProduct.lift.symm u) := (LinearEquiv.apply_symm_apply _ _).symm
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul]
    refine Good.smul a ?_
    rw [hu', PiTensorProduct.lift.tprod]
    exact ⟨(hT.aut x).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut x) (hT.cusp x), (hT.aut x).left,
      hT.lev x⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy

theorem conj_eq_one_iff' (z : ℂ) : conj z = 1 ↔ z = 1 := by
  constructor
  · intro h; simpa using congrArg conj h
  · intro h; simp [h]

theorem conj_values_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s =>
    (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧
      (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧
      ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧
    (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔
      Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧
    ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ),
      heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => good_val hP hc.inf (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v, fun P d R => ?_, fun R f => ?_⟩
  · simp only [Hecke₂, conj_eq_one_iff']
  · funext g
    set_option synthInstance.maxHeartbeats 100000 in
      simp [heckeLin, map_sum]

end GlobalTheory.ConjVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem valued_natCast_eq_one {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    Valued.v (N : v.adicCompletion K) = 1 := by
  have e : (N : v.adicCompletion K) = ((algebraMap R K (N : R) : K) : v.adicCompletion K) := by
    rw [map_natCast]; exact (map_natCast (algebraMap K (v.adicCompletion K)) N).symm
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hN ((v.intValuation_lt_one_iff_mem _).1 h))

theorem natCast_ne_zero_of {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K) ≠ 0 := fun h => by
  have := valued_natCast_eq_one (K := K) hN
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem inv_natCast_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hN, inv_one]

theorem latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}
    (hN : (N : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latLoc F L v ≤ latLoc F L' v := by
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hN0 := natCast_ne_zero_of (K := F) hN
  have e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * (N : Fv F v)⁻¹) ⊗ₜ[F] (((N : E) • x) i) := by
    funext i
    rw [Pi.smul_apply, show (N : E) • x i = (N : F) • x i by
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast], TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_natCast]
    congr 1
    field_simp
  rw [e]
  exact tmul_mem_latLoc (mul_mem ha (inv_natCast_mem hN)) (h x hx)

theorem latAt_le {L L' : Submodule (𝓞 E) (Fin n → E)} {w : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∉ w.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latAt w L ≤ latAt w L' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have hN0 := natCast_ne_zero_of (K := E) hN
  have hm : (⟨(N : w.adicCompletion E)⁻¹, inv_natCast_mem hN⟩ : Ov E w) •
      (fun i => algebraMap E (w.adicCompletion E) (((N : E) • x) i)) = fun i => algebraMap E (w.adicCompletion E) (x i) := by
    funext i
    change (N : w.adicCompletion E)⁻¹ * algebraMap E _ ((N : E) • x i) = _
    rw [smul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ hN0]
  change (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ latAt w L'
  rw [← hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h x hx, rfl⟩)

end GlobalTheory.LatAgree

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem stabLoc_congr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (hs : latLoc F L v = latLoc F L' v) : stabLoc σ J L v = stabLoc σ J L' v := by
  simp only [stabLoc, hs]

theorem isParamVec_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (hs : latLoc F L v = latLoc F L' v) (ha : latAt w L = latAt w L') {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (B : Multiset ℂˣ) :
    IsParamVec σ J L h ρ x B ↔ IsParamVec σ J L' h ρ x B := by
  have hst := stabLoc_congr σ J hs
  simp only [IsParamVec, IsSplitChart, IsInertChart, IsFrameAt, hst, ha]

theorem isParamFun_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (HeightOneSpectrum (𝓞 F))} (hs : ∀ v ∉ S, latLoc F L v = latLoc F L' v)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L')
    {V : Type} [AddCommGroup V] [Module ℂ V] (f : GAd σ J → V) (c : Fam E) :
    IsParamFun σ J L S f c ↔ IsParamFun σ J L' S f c := by
  unfold IsParamFun IsParamVecOff
  refine forall₂_congr fun v hv => forall₂_congr fun w h => ?_
  exact isParamVec_congr h (hs v hv) (ha w (h ▸ hv)) _ _ _

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem latLoc_latAt_eq {L L' : Submodule (𝓞 E) (Fin n → E)} {S : Set (HeightOneSpectrum (𝓞 F))} {N : ℕ}
    (h₁ : ∀ x ∈ L, (N : E) • x ∈ L') (h₂ : ∀ x ∈ L', (N : E) • x ∈ L)
    (hN : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → (N : 𝓞 E) ∉ w.asIdeal) :
    (∀ v ∉ S, latLoc F L v = latLoc F L' v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L' := by
  refine ⟨fun v hv => ?_, fun w hw => le_antisymm (latAt_le (hN w hw) h₁) (latAt_le (hN w hw) h₂)⟩
  obtain ⟨w, rfl⟩ := exists_under_eq (E := E) v
  have hv' : (N : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hN w hv (by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h)
  exact le_antisymm (latLoc_le hv' h₁) (latLoc_le hv' h₂)

end GlobalTheory.LatAgree

namespace GlobalTheory.ChainOnto

theorem stabLoc_isParamFun_frameLat : ∀ D : D7, ForStage D fun c _ s =>
    (∀ v ∉ c.S, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v =
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram (GlobalTheory.AdelicU.frameLat s.V) v) ∧
    ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := by
  intro D c _ j _ s hs
  obtain ⟨N, ⟨-, -, -, h₁, h₂⟩, hN⟩ := hs.base
  have h₁' : ∀ x ∈ GlobalTheory.AdelicU.frameLat s.V, (N : D.host.E) • x ∈ s.Λ := fun x hx =>
    h₁ x (by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hx)
  have h₂' : ∀ x ∈ s.Λ, (N : D.host.E) • x ∈ GlobalTheory.AdelicU.frameLat s.V := fun x hx => by
    have := h₂ x hx
    rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice] at this
    exact this
  obtain ⟨hloc, hat⟩ := GlobalTheory.LatAgree.latLoc_latAt_eq (S := (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) h₂' h₁'
    (fun w hw => hN w hw)
  exact ⟨fun v hv => GlobalTheory.LatAgree.stabLoc_congr _ _ (hloc v hv),
    fun f B => GlobalTheory.LatAgree.isParamFun_congr hloc hat f B⟩

end GlobalTheory.ChainOnto
end

