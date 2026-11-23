module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedLatticeDiagonalBasePointMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_row {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (K U : Fin n → P.adicCompletion E)
    {c s : 𝓞 E ⧸ P.asIdeal} (hK : ∀ j, HasRes P (K j) (if j = r then c else 0)) (hU : ∀ j, Valued.v (U j) ≤ 1)
    (hs : HasRes P (U r) s) : HasRes P (∑ j, K j * U j) (c * s) := by
  obtain ⟨s, rfl, hs⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, DilPt.hasRes_mk_iff]
  have hC : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : (∑ j, K j * U j) - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (c * s)) =
      ∑ j, (K j - if j = r then algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) else 0) * U j +
        algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E c) *
          (U r - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_) ?_
  · rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right' (hU j)) ?_
    have := hK j
    by_cases hj : j = r
    · rw [if_pos hj, DilPt.hasRes_mk_iff] at this
      rwa [if_pos hj]
    · rw [if_neg hj] at this
      rw [if_neg hj, sub_zero]
      exact DilPt.hasRes_lt_one this
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hC) hs

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoSet_ext {d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} (hN : d.1.N = d'.1.N) (hf : ∀ P, ∀ x ∈ d'.1.N, d.1.f P x = d'.1.f P x)
    (hbe : ∀ w, ∀ x ∈ d'.1.N, d.1.be w x = d'.1.be w x) : d = d' := by
  have hat : ∀ P, d.1.at P = d'.1.at P := fun P => by unfold Deco.at; rw [hN]
  have h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E), s ∉ P.asIdeal → Ideal.Quotient.mk P.asIdeal s ≠ 0 :=
    fun P s hs h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  refine Subtype.ext (Deco.ext hN (funext fun P => funext fun x => ?_) (funext fun P => funext fun x => ?_))
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hf P _ h
      rw [d.2.f_smul P s x (hat _ ▸ hx), d'.2.f_smul P s x hx] at this
      have hp := P.1.isPrime
      exact mul_left_cancel₀ (h0 _ s hs) this
    · rw [d.2.f_off P x (hat _ ▸ hx), d'.2.f_off P x hx]
  · by_cases hx : x ∈ d'.1.at P.1
    · obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hx
      have := hbe P _ h
      rw [d.2.be_smul P s x (hat _ ▸ hx), d'.2.be_smul P s x hx] at this
      have hp := P.1.isPrime
      funext i
      exact mul_left_cancel₀ (h0 _ s hs) (congrFun this i)
    · rw [d.2.be_off P x (hat _ ▸ hx), d'.2.be_off P x hx]

theorem decoOf_dia_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g k : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) (c : DiaG (E := E) (ST := ST)), IsPtOf hc (g * k) p → (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = Formalism.L2.Col.stdLat E n) → (∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → g ∈ UAd hc n ∧ (decoOf ST SG g).dia c = p.deco := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g k p c h ⟨p₀, hk, hk0⟩ htriv hrow
  classical
  have hg : g ∈ UAd hc n := by
    have := mul_mem h.uni (inv_mem hk.uni)
    rw [mul_inv_cancel_right] at this
    exact this
  have hkc := hk.lat
  rw [hk0] at hkc
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (mem_globLat g w).trans ((hkI _).trans ?_)
    have e : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Formalism.L2.Col.pullV g w =
        GlobalTheory.Mem.Col2.pullV (g * k) w := (DilPt.pullbackVector_mul_right g k w).symm
    rw [e]
    refine (mem_latS_std _).symm.trans ((h.lat _).symm.trans ?_)
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hone : ∀ w ∈ SG, ∀ i j, adAt F w ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if j = i then 1 else 0 := by
    intro w hw i j
    have h1 : bc (prV (E := E) (w.under (𝓞 F))) k⁻¹ = 1 := by rw [map_inv, htriv w hw, inv_one]
    have h2 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0 := by
      have := congrArg (fun x : GL (Fin n) _ => x.1 i j) h1
      simp only [Units.val_one, Matrix.one_apply] at this
      exact this
    have h3 : prV (E := E) (w.under (𝓞 F)) ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j - if j = i then 1 else 0) = 0 := by
      rw [map_sub, h2]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h3 w rfl
    rw [map_sub, sub_eq_zero] at h4
    rw [h4]
    split_ifs <;> simp
  have hraw := rlc_decoOf_val hc n ST SG hg
  have hint : ∀ x ∈ p.deco.1.N, ∀ i, GlobalTheory.Mem.Col2.pullV g x i ∈ RInt F E := fun x hx =>
    (mem_globLat g x).1 (hN ▸ hx)
  refine ⟨hg, decoSet_ext ?_ (fun P x hx => ?_) fun w x hx => ?_⟩
  · show (decoOf ST SG g).1.N = _
    rw [hraw]
    exact hN
  · show (c P).1 * (decoOf ST SG g).1.f P x = _
    have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
    have h1 := h.f P x hx _ hl
    rw [DilPt.pullbackVector_mul_right] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1
    have h2 := hasRes_row (lastIdx n) _ (fun j => adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x j)) (fun j => hrow P _ j hl)
      (fun j => (mem_rInt_iff F E _).1 (hint x hx j) P.1) (PtExist.hasRes_redA P.1 (hint x hx _))
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    exact h2.unique h1
  · show (decoOf ST SG g).1.be w x = _
    rw [hraw]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ (hN ▸ hx))]
    funext i
    have h1 := h.be w x hx i
    rw [DilPt.pullbackVector_mul_right] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hone w.1 w.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact (PtExist.hasRes_redA w.1 (hint x hx i)).unique h1

end GlobalTheory.Mem.Col2.DiaPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitFrameW

theorem eq_of_mul_eq_one {K : Type} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (h1 : A * B = 1) (h2 : B * A = 1) : m = n := by
  let e : (Fin n → K) ≃ₗ[K] (Fin m → K) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

theorem complMap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)
    (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E) (hc : Continuous c)
    (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (h : s.w.under (𝓞 (maximalRealSubfield E)) = s.v)
    (a : s.v.adicCompletion (maximalRealSubfield E)) : GlobalTheory.LFun.complMap h a = c a := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).equalizer
    (GlobalTheory.LFun.SplitChart.continuous_complMap h) hc (funext fun k => ?_)) a
  change GlobalTheory.LFun.complMap h (algebraMap _ _ k) = c (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap, ← hci]
  congr 1
  exact s.i.commutes k

theorem under_w {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E) :
    s.w.under (𝓞 (maximalRealSubfield E)) = s.v :=
  HeightOneSpectrum.ext s.w_under

theorem cpt_swap {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E)
    (Φ : FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E →+* FiniteAdeleRing (𝓞 E) E)
    (hΦ : ∀ (a : FiniteAdeleRing (𝓞 F1) F1) (x : E),
      Φ (a ⊗ₜ[F1] x) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (s : SplitPlace E) (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E)
    (hc : Continuous c) (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (y : AL E) :
    Φ ((swapCast hF).symm y) s.w = c (s.proj y) := by
  subst hF
  induction y using TensorProduct.induction_on with
  | zero =>
    simp
    rfl
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hy, ← hz]
    rfl
  | tmul x a =>
    change Φ (a ⊗ₜ x) s.w = c (s.i x * ReciprocityTheory.Aut.evalAt E s.v a)
    rw [hΦ, map_mul, hci]
    change algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap _ E a s.w = _
    rw [GlobalTheory.DefU.ClassFin.adMap_eq_complMap (under_w s), complMap_eq s c hc hci]
    rfl

end GlobalTheory.SplitFrameW

namespace GlobalTheory.SplitFrameW


set_option maxHeartbeats 2000000 in
theorem main : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β hS s
  obtain ⟨⟨βs, βs', h1, h2, hfr⟩, -⟩ := hS
  obtain ⟨c, hc, hc', hci⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv D.host.E s
  obtain ⟨f, hf⟩ : ∃ f : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* s.w.adicCompletion D.host.E,
    f = (GlobalTheory.StdFrames.cpt s.w).comp (swapAE D) := ⟨_, rfl⟩
  have hn : V.rank = n := eq_of_mul_eq_one (βs.map f) (βs'.map f)
    (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)])
  subst hn
  obtain ⟨Φc, hΦc⟩ : ∃ Φc : Matrix (Fin V.rank) (Fin V.rank) (EAf D) →+*
      Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    Φc = (c.symm.toRingHom.comp (GlobalTheory.StdFrames.cpt s.w)).mapMatrix := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B = βs.map (swapAE D) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B' = βs'.map (swapAE D) := ⟨_, rfl⟩
  have hBB : B * B' = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : B' * B = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨X, hX⟩ : ∃ X, X = Φc ((β⁻¹).val * B) := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X', X' = Φc (B' * β.val) := ⟨_, rfl⟩
  have hXX : X * X' = 1 := by
    rw [hX, hX', ← map_mul, show (β⁻¹).val * B * (B' * β.val) = (β⁻¹).val * (B * B') * β.val by
      simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, Units.inv_mul, map_one]
  have hXX' : X' * X = 1 := by
    rw [hX, hX', ← map_mul, show B' * β.val * ((β⁻¹).val * B) = B' * (β.val * (β⁻¹).val) * B by
      simp only [Matrix.mul_assoc], Units.mul_inv, Matrix.mul_one, hBB', map_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    g = ⟨X', X, hXX', hXX⟩ := ⟨_, rfl⟩
  refine ⟨g, fun κ _ hk a b => ?_⟩
  have hK : Φc (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (swapAE D)) =
      ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) := by
    rw [hΦc]
    refine Matrix.ext fun i j => ?_
    change c.symm (((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) ((swapCast hF).symm (κ.1.val i j)) s.w) = s.proj (κ.1.val i j)
    rw [cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci]
    exact c.symm_apply_apply _
  have e1 : (finE V (P.ψ κ)).val = B * (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (swapCast hF).symm).map (swapAE D)) * B' := by
    change (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (swapAE D) = _
    rw [hfr κ, Matrix.map_mul, Matrix.map_mul, hB, hB']
  have hM : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) = X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [Units.val_mul, Units.val_mul, e1, ← hK, hX, hX', ← map_mul, ← map_mul]
    simp only [Matrix.mul_assoc]
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 hk a b
  have e3 : (↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) =
      X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [hg]; rfl
  have hent : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) a b =
      c.symm (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) := by
    rw [hΦc]; rfl
  have e2 : GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) =
      c (((↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) - 1) a b) := by
    rw [e3, ← hM, Matrix.sub_apply, hent, map_sub, map_sub, c.apply_symm_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2]
  by_contra hne
  push_neg at hne
  have := GlobalTheory.FixedAtSplit.valued_lt_one_of_map c.symm hc' (c _) (by rw [c.symm_apply_apply]; exact hv)
  exact absurd this (not_lt.2 hne)

end GlobalTheory.SplitFrameW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCouplingCosetWithGivenReduction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart.CosetLift

section Local

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e / (m : E)) := by
  have h0 : P.intValuation (m : 𝓞 E) ≠ 0 := P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)
  refine ⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩
  have hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
    have h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E) := by
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
    exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

theorem exists_one_intAt_div (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ e : 𝓞 E, Ideal.Quotient.mk w.asIdeal e = 1 ∧
      ∀ w' ∈ T, w' ≠ w → Formalism.L2.Col.IntAt w' (algebraMap (𝓞 E) E e / (m : E)) := by
  classical
  choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm
  have ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal) := by
    intro w'
    by_cases hne : w' = w
    · exact ⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩
    · by_contra hc
      refine hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))
      by_contra h'
      exact hc ⟨t, h', fun _ => h⟩
  choose t ht1 ht2 using ht
  have := w.isMaximal
  have := w.isPrime
  have he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal :=
    w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem exists_vec (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ y : Sp E n, ∀ w : SG, ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1 ∧
      d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = v w := by
  classical
  choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)
  choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1)
    (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))
  refine ⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩
  have hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) =
      algebraMap (𝓞 E) E (e w0) := mul_div_cancel₀ _ TopStep.qOf_ne_zero
  have hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1
      (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E))) := fun w => by
    by_cases h : w = w0
    · rw [h, hc]
      exact Formalism.L2.Col.IntAt.coe _ _
    · exact (TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))
  have hx : ∀ w : SG, x w ∈ d.1.at w0.1 := fun w => Formalism.L2.Col.le_locP _ _ (hxN w)
  simp only [Finset.smul_sum, smul_smul]
  refine ⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩
  rw [TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]
  · rw [TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]
  · intro w _ h
    rw [TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _)
      (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem coset_be (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (SB : Finset (HeightOneSpectrum (𝓞 E))) (w : SG) (hw : w.1 ∈ SB) (e0 : SB → ℤ)
    (h0 : e0 ⟨w.1, hw⟩ = 0) {y : Sp E n} (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1) :
    {v | ∃ z ∈ {z | z - y ∈ Formalism.L2.Col.locLat SB d.1.N e0}, v = d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)} =
      {d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y)} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - y ∈ d.1.at w.1 := by
      have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩
      rwa [h0, zpow_zero, inv_one, one_smul] at this
    have e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z =
        ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'),
      TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · intro hv
    exact ⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩

end Local

theorem exists_ptAt_bar_eq {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (_hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2)
    (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    have hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P =>
      (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩
    obtain ⟨y', hy'⟩ := exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)
    refine ⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N
      (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩
      rw [if_pos (hG' P), _root_.zpow_neg_one, inv_inv]
      exact (hy' ⟨P.1, hG' P⟩).1
    · funext w
      have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩
      rw [if_pos w.2, _root_.zpow_neg_one, inv_inv] at h1
      refine (coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_
      rw [(hy' w).2, MemChart.bar, hY]
      exact (coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm
  · have hY : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩
    funext w
    simp [MemChart.bar, hY]

end GlobalTheory.Mem.Col2.MemChart.CosetLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

end GlobalTheory.Mem.Col2.ChiFinTop

end
end

