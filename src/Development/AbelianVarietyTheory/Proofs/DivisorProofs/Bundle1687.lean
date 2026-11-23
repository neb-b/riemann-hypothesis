module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation

namespace GlobalTheory.SupFull

section Generic

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R]

theorem exists_smul_nonneg_of_pow (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (S : Set R)
    (hS : ∀ g ∈ S, ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • g)) (f : R) (k : ℕ)
    (hf : f ^ (k + 1) ∈ Submodule.span K S) : ∃ s : K, s ≠ 0 ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v (s • f) := by
  have h1 : Submodule.span K S ≤ Submodule.span K (latIn ⊤ Vs hV : Set R) := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨s, hs, h⟩ := hS g hg
    rw [← inv_smul_smul₀ hs g]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨trivial, h⟩))
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ (h1 hf)
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul K] at ht
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero t.2
  refine ⟨_, ht0, fun la v hv => ?_⟩
  have h2 := ((mem_latIn _ _ _ _).1 ht).2 la v hv
  have hv' := hV la v hv
  rw [hv'.smul _ _ ht0] at h2 ⊢
  by_cases htop : v f = ⊤
  · rw [htop, EReal.coe_add_top]; exact le_top
  obtain ⟨x, hx⟩ : ∃ x : ℝ, v f = x := ⟨_, (EReal.coe_toReal htop (hv'.ne_bot f)).symm⟩
  have h3 : ∀ m : ℕ, v (f ^ (m + 1)) = ((((m : ℝ) + 1) * x : ℝ) : EReal) := fun m => by
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ, hv'.mul, ih, hx, ← EReal.coe_add]
      congr 1; push_cast; ring
  have h4 : (0 : ℝ) ≤ (vAdd la (algebraMap (𝓞 K) K t) : ℤ) := by exact_mod_cast vAdd_int_nonneg la ht0
  rw [h3, ← EReal.coe_add, EReal.coe_nonneg] at h2
  rw [hx, ← EReal.coe_add, EReal.coe_nonneg]
  rcases le_total 0 x with h | h
  · linarith
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (neg_nonneg.2 h)]

theorem fg_latIn (C : Submodule K R) [FiniteDimensional K C] (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : ∀ x ∈ C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (φ : R →ₗ[K] K'),
      φ x ≠ 0 ∧ ∀ y ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v y) → IsIntegral ℤ (φ y)) : (latIn C Vs hV).FG := by
  refine Submodule.FG.map _ (GlobalTheory.fg_of_integral_functionals K C _ fun x hx => ?_)
  obtain ⟨K', _, _, _, φ, h0, h1⟩ := h x.1 x.2 fun e => hx (Subtype.ext e)
  exact ⟨K', inferInstance, inferInstance, inferInstance, φ ∘ₗ C.subtype, h0, fun y hy => h1 y.1 y.2 hy⟩

end Generic

theorem pow_mem_cusp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) (k : ℕ) :
    ∃ a', Dom a' ((k + 1) * n) ∧ f ^ (k + 1) ∈ cusp Xo c U a' ((k + 1) * n) := by
  have hM : CuspMul Xo c U := (Formalism.L2.PjFree.cuspMul_ofPj U).1 (GlobalTheory.CuspProduct.cuspMul_holds E H Dw l Xo c r _)
  induction k with
  | zero => exact ⟨a, by simpa using hd, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨a', h1, h2⟩ := ih
    rw [Nat.succ_mul, pow_succ]
    exact ⟨a' + a, ⟨fun τ => (h1.1 τ).add (hd.1 τ), h1.2.add hd.2⟩, hM _ _ _ _ _ _ h1 hd h2 hf⟩

theorem exists_unf (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) (hj : InR D j) :
    ∃ U : Formalism.L2.PjFree.Unf (Q.Xo j) Q.c Q.c.F.val.toRingHom D.R.r, Formalism.L2.PjFree.IsUnf U ∧
      (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) Q.l.M) ∧
      (∀ k la γ, (U.X k).χ la γ = 1) ∧
      ∀ k, ∃ (Xx : DataX D.host.E D.R.r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
        Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧
        Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  obtain ⟨-, -, hM', -, hx1, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
    have : cc (-D.host.xi0) = -cc D.host.xi0 := by simp [cc]
    rw [this, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]
  have hneg : ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
    intro τ hτ
    rw [hQ.1.2.1, hQ.1.2.2.1] at hτ
    have h := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [h0]
      simpa using d_pos D
    rw [if_pos hpos, Int.cast_one, one_mul] at h
    simpa using h
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum _ Q.H (Q.Dw j) (-(-D.host.xi0))
    (by rw [neg_neg, GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D]) (by rw [neg_neg]; exact cmHost_imaginaryGenerator_ne_zero hP D) _ hr.symm
  obtain ⟨U, hU, hPr, -, hχ, hG, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    Q.c.F.val.toRingHom D.R.r (-D.host.xi0) Gm φ (by omega) rfl hξ hneg hφ
  rw [hM'] at hPr
  refine ⟨U, hU, fun k k' => ⟨(hG k).1.trans (hG k').1.symm, (hG k).2.trans (hG k').2.symm⟩,
    fun k ga hga h => ?_, hχ, fun k => ?_⟩
  · refine hPr k ga hga fun x hx => ?_
    obtain ⟨u, hu, e⟩ := h x hx
    exact ⟨u, hu, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  · have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ _ _ U hU k
    have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (U.X k).ξ0 * D.host.AA *
        D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
      rw [(hG k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact hP D.R D.host
    have hM : 0 < Q.l.M := by have := Q.l.three_le; omega
    obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ (U.X k) D.host.AA D.host.AAbar
      (xiR D) Q.l.M
      (fun a => by
        rw [GlobalTheory.LatticeData.cc_eq_conj]
        exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
      hone (fun τ => by rw [(hG k).2, map_neg, norm_neg]; exact xiConst_holds D τ) hx1 hperf.1 hperf.2 hM (hPr k)
    exact ⟨Xx, _, h1, AA_ne_zero hP D, h3⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem fullAt_of_pins (D : D7) (T : Core D) (hQ : T.Q.Pins) (j : ℕ) (hj : InR D j)
    (hU : IsUnf (T.U j T.σ₀)) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) : FullAt T j w := by
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hQ
  obtain ⟨hr, hr1, -⟩ := hnum j hj
  obtain ⟨U', hU', hG, hPr, hχ, hX⟩ := exists_unf D T.Q hQ j hj
  have hbdd : ∀ a n, Dom a n → ∀ f ∈ T.cuspA j a n,
      ∀ k, (U'.X k).IsBddSec (laU U'.toPj a n k) (rdU U'.toPj f k) := fun a n hd f hf =>
    isBddSec_of_isUnf _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀ _ (T.U j T.σ₀) U'.toPj T.good_σ₀ hU hU' (by omega) a n hd f
      (cusp_le_sec _ _ _ _ _ hf) fun k =>
        (Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ (((mem_cusp _ _ _ _ _ f).1 hf).2 _ T.good_σ₀) k).1
  constructor
  · haveI : FiniteDimensional T.Q.c.F (cuspW T j w) :=
      GlobalTheory.cuspForms_finiteDimensional_of_goodEmb _ _ _ _ _ _ _ (T.U j) T.σ₀ T.good_σ₀ hU _ _ (dom_wtA w)
    refine fg_latIn _ _ _ fun x hx hx0 => ?_
    letI := T.Q.H.starRing
    have hs := cusp_le_sec _ _ _ _ _ hx
    obtain ⟨z, La, hz, hG0⟩ := GlobalTheory.CMDetect.exists_good_cmPt_frPoly_ne_zero _ _ _ _ (T.Q.Xo j) T.Q.c (fun _ => rfl) _
      U'.toPj hU' hr1 hX _ _ x hs hx0 (hbdd _ _ (dom_wtA w) x hx)
    obtain ⟨y, N, h0, hint⟩ := GlobalTheory.LatFull.CMInt.exists_frame_bounded_denom _ _ _ _ (T.Q.Xo j) T.Q.c z _ La hz _ _ x
      hs hG0
    refine ⟨z.K, inferInstance, inferInstance, inferInstance,
      { toFun := fun F => N * evR (T.Q.Xo j) T.Q.c F y
        map_add' := fun F G => ?_
        map_smul' := fun s F => ?_ }, h0, fun F hF => hint F (cusp_le_sec _ _ _ _ _ hF)⟩
    · rw [← mul_add]
      exact congrArg _ (evalAt_add _ _ F G y)
    · have e : evR (T.Q.Xo j) T.Q.c (s • F) y = algebraMap T.Q.c.F z.K s * evR (T.Q.Xo j) T.Q.c F y :=
        evalAt_smul _ _ s F y
      rw [e, RingHom.id_apply, Algebra.smul_def, mul_left_comm]
  · refine le_antisymm (Submodule.span_le.2 fun f hf => ((mem_latIn _ _ _ f).1 hf).1) fun f hf => ?_
    obtain ⟨a', hd', hf'⟩ := pow_mem_cusp (T.U j) (dom_wtA w) hf (4 * (Module.finrank ℚ D.host.E * D.R.r) + 3)
    obtain ⟨d, nab, hlev, hnab, hroot, hle, hph, hspan⟩ := exists_datum_span _ _ _ _ (T.Q.Xo j) T.Q.c _ _ U' hr1 hA
      T.good_σ₀ hU' hG hPr a' _ hd' (Nat.le_mul_of_pos_right _ hn) fun k ga _ => hχ k _ ga
    have hsf : Squarefree d.l₂.M := by
      rw [hle, hQ.2.1.1,
        Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
      exact ⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩
    obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_pow (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) isVal_valSet _
      (exists_smul_short_nonneg D _ _ _ (T.Q.Xo j) T.Q.c _ d hlev hnab hroot hsf hph nab 1 0 a') f _
      (hspan _ (cusp_le_sec _ _ _ _ _ hf') (hbdd _ _ hd' _ hf'))
    rw [← inv_smul_smul₀ hs f]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latIn _ _ _ _).2 ⟨Submodule.smul_mem _ _ hf, h⟩))

end GlobalTheory.SupFull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRuleAnyLevel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv

open GlobalTheory.IntCuspLat

namespace GlobalTheory.LargeCover

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem factorisation_pow (Xo : Moduli Dw l) (N ℓ : ℕ) (hodd : Odd N) (hMN : l.M ∣ N) (hp : ℓ.Prime) :
    ∃ (u n' Bn j : ℕ) (β : 𝓞 E), u ∣ l.M ∧ Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * u * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧
      u ^ 2 * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) →
        t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * u ^ 2) = 1 := by
  have hN : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨e, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN ℓ hp.ne_one
  obtain ⟨a, m, hm', hMa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hp.ne_one
  have hcop : Nat.Coprime n' ℓ := ((hp.coprime_iff_not_dvd).2 hn').symm
  have hcm : Nat.Coprime m ℓ := ((hp.coprime_iff_not_dvd).2 hm').symm
  have hdv : ℓ ^ a * m ∣ ℓ ^ e * n' := by rw [← hMa, ← hNe]; exact hMN
  obtain ⟨k, hk⟩ := (hcm.pow_right e).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hdv)
  have hae : a ≤ e := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
    ((hcop.symm.pow_left a).dvd_of_dvd_mul_right ((Dvd.intro _ rfl).trans hdv))
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hae
  refine ⟨ℓ ^ a, n', ℓ ^ (2 * b), 2 * (a + b), (ℓ : 𝓞 E) ^ b, ⟨m, hMa⟩, hcop, ?_, ?_, by ring, fun T t ht => ⟨?_, ?_⟩⟩
  · rw [hNe]; push_cast; ring
  · rw [map_pow, map_natCast]; push_cast; ring
  · obtain ⟨k', hk'⟩ := hMN
    have := GlobalTheory.TorsFac.kill Xo t N ht (N : 𝓞 E)
      (by rw [hk', Nat.cast_mul]; exact l.Mb.mul_mem_right _ (GlobalTheory.TorsFac.M_mem l))
    rw [← GlobalTheory.TorsFac.act_nat, ← this]
    congr 2
    push_cast; ring
  · have := GlobalTheory.TorsFac.kill Xo t N ht (l.M * k) (l.Mb.mul_mem_right _ (GlobalTheory.TorsFac.M_mem l))
    rw [GlobalTheory.TorsFac.act_pow, ← this]
    congr 2
    rw [hNe, hMa, hk]; push_cast; ring

theorem class_bound_any_level (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨u, n', Bn, j, β₀, hu, h1, h2, h3, h4, h5⟩ := factorisation_pow Xo N ℓ hL.1 hL.2.1 hℓ
  have hA : (u : 𝓞 E) * H.bar (u : 𝓞 E) = ((u ^ 2 : ℕ) : 𝓞 E) := by rw [map_natCast]; push_cast; ring
  have h := sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
    hz hg (fun b => (h5 _ _ (hk b)).1) hF htr n' (u ^ 2) Bn j _ β₀ h1 h2 hA h3 h4 (fun b => (h5 _ _ (hk b)).2)
  obtain ⟨m, hm⟩ := hu
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point


open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in
theorem exists_smul_nonneg_of_shortRule_any_level (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q))
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∃ t : c.F, t ≠ 0 ∧ ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (t • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hM0 : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  have hS : ∀ p ∈ D.host.condN.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = (NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ∏ p ∈ D.host.condN.primeFactors, p ^ X := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q hq)
  refine ⟨betaH (Dw := Dw) c Λ * ((Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) : ℕ) : c.F),
    mul_ne_zero hβ (by exact_mod_cast mul_ne_zero hc0 (mul_ne_zero hQ0 (pow_ne_zero _ hM0))), ?_⟩
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have key := fun q => class_bound_any_level d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (htp q) (hF q) htr
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ, vV_prod_pow T' X _ hS, Int.cast_sum,
      Finset.sum_div]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : (0 : ℝ) ≤ (vV T'.V (p : T'.Fr) : ℝ) / ((r * e : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p) (Nat.cast_nonneg _)
    have h2 : D.host.vdH p ≤ ((NumberField.discr D.host.E).natAbs : ℝ) :=
      (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Module.finrank_pos)).trans
        (by
          have h : padicValNat p (NumberField.discr D.host.E).natAbs ≤
              (NumberField.discr D.host.E).natAbs := by
            rw [Nat.padicValNat_def]
            exact Nat.multiplicity_le_self _
          exact_mod_cast h)
    have h3 := D.host.vdH_nonneg p
    have h4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) := Nat.cast_nonneg _
    rw [Int.cast_mul, Int.cast_natCast, mul_div_assoc (X : ℝ), hX, Nat.cast_mul (NumberField.discr D.host.E).natAbs]
    have h5 := mul_nonneg (mul_nonneg h1 h3) h4
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1) h4
    linarith
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.LargeCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOnBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section ClassSum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem j_thetaMat_base (hB : BaseLinks R F) (j : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L j t).dZ (liftLvl F) (liftSub R F j t)) → D.what₂.LL) :
    (R.FW j).j (sg0 D A) (coordMap R F j ((thetaMat R F j t).mulVec y)) =
      R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y)) := by
  have k0 := j_coordMap (R := R) (F := F) j ((thetaMat R F j t).mulVec y)
  have k1 := (R.toCx F).key_lift F.cr false hB.1 hB.2.1 j t y
  have k2 := tC_cpt (R.toCx F) F.cr false j t y
  have k3 : (R.toCx F).θ' j t ((R.toCx F).jL j t (F.cr.toL (R.toCx F).zs false j t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG j t (R.jV j t ((A.fam.L j t).toF (liftLvl F) (liftSub R F j t) y))) := rfl
  exact k0.trans ((k1.trans k2).trans k3)

theorem eq_thetaOp_base {s : ℕ} (hOk : A.fam.Ok s) (hHV : R.models_HV) (hjV : R.models_jV) (hU : R.LUnif) (hB : BaseLinks R F)
    (i : Fin D.R.m) (t : T0) (x : Fin (OntoChain.srcDim F i t) → D.what₂.LL) {u : Fin (R.nW i) → D.what₂.LL}
    (hu : u ∈ R.WL F false i) (ha : (R.FW i).j (sg0 D A) u = R.thG i t (R.jV i t (srcF F i t x))) :
    u = thetaOp R F i t x := by
  rw [← range_coordMap] at hu
  obtain ⟨z, rfl⟩ := hu
  obtain ⟨y, rfl⟩ : ∃ y, (thetaMat R F i t).mulVec y = z := ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false)
    (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1 hB.2.1 i t).2 z
  have hb : _ = R.thG i t (R.jV i t (srcF F i t (((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y))) :=
    (j_thetaMat_base hB i t y).trans (congrArg (fun f => R.thG i t (R.jV i t f)) (toF_eq_srcF hOk i t y))
  have h0 := lPr_eq_zero_of_ker hOk hHV hjV i t (x - ((A.fam.L i t).lE (liftLvl F) (liftSub R F i t)).mulVec y)
    ((lift_sub i t _ _).trans (sub_eq_zero.2 (ha.symm.trans hb)))
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, BlockDat.lf_lPr_lE (blockHyp (F := F) hOk i t), Matrix.one_mulVec,
    sub_eq_zero] at h0
  rw [← h0, Matrix.mulVec_mulVec]
  rfl

theorem goodOp_classSum_base {s : ℕ} (hOk : A.fam.Ok s) {ph : Fin D.R.m → ℂ} (hG : PhasedLift R ph) (hHV : R.models_HV)
    (hjV : R.models_jV) (hHW : R.models_HW) (hU : R.LUnif) (hB : BaseLinks R F) (i : Fin D.R.m) (t : T0)
    {θ : (Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : OnTies.IsClassSum R i t F.P0 F.ψ0⁻¹ (ph i) θ) (x : Fin (OnTies.srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL)
    (hx : goodOp R i (θ x) ∈ R.WL F false i) : goodOp R i (θ x) = thetaOp R F i t x := by
  refine eq_thetaOp_base hOk hHV hjV hU hB i t x hx ((hHW i _).1 ?_)
  refine (adForm_goodOp hU i _).trans ?_
  refine (congrArg (Mult.postOn _ (R.eWf i (sg0 D A))) (hθ x)).trans ?_
  exact (LinearMap.map_smul _ _ _).trans (hG i t _).symm

end ClassSum

section Tied

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst} {s : ℕ}

theorem exists_tieCoord_base {P : Type} [Group P] [Finite P] {inc : P →* G} {O : OnObj ((R.toCx F).data F.cr false) P c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph inc O) (hinc : F.P0 ≤ inc.range)
    (hOk : A.fam.Ok s) (h1 : R.grp_levels F) (h2 : R.grp_chiW) (hHV : R.models_HV) (hjV : R.models_jV) (hHW : R.models_HW)
    (hμ : R.tup_mu_conj) (hG : PhasedLift R ph) (hU : R.LUnif) (hB : BaseLinks R F)
    (hrat : TwistedRational R F ph) (hI : LeafIdentity O) (hT : LeafTW2 O) : ∃ w, TieCoord (withCoord O w) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  let w : ∀ j, (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) := fun j =>
    LinearEquiv.ofBijective (toForms (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
      (toForms_bijective (T := (run v₁).full) (R := R) (h v₁) fw j (z j))
  have he : ∀ j x, w j (O.e j x) = goodOp R j (w j x) := fun j x => (ht v₁ j).1.e_eOp x
  have hZ : ∀ j x, x ∈ O.Zg j ↔ w j x ∈ R.WL F false j := fun j =>
    mem_Zg_iff h1 h2 hinc j ((ht v₁ j).1.rho_eq_of_actionPin (ht v₁ j).2) (ht v₁ j).1.U_eq (ht v₁ j).1.ψ_eq (he j)
      (ht v₁ j).1.V₀_eq
  have hM : ∀ j x, x ∈ O.Ms j ↔ w j x ∈ supLat (R.FW j) := fun j x => mem_Ms_iff (ht v₁ j).1 x
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j) →
      (O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)) →
      IsLatIn (O.Zg j) (O.Im v j) → (withCoord O w).TjId j v (R.mu v) := fun v j hra hI hT => by
    refine coord_tuple j v (y v j) (fun x => by rw [(ht v j).1.Mt_eq]; rfl) (fun x hx => ?_) hI
    have hθ : OnTies.IsClassSum R j (R.mu v) F.P0 F.ψ0⁻¹ (ph j)
        ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) := (ht v j).1.θ'_eq hra
    have e : ((w j).toLinearMap ∘ₗ O.θ' v j ∘ₗ (y v j).symm.toLinearMap) (y v j x) = w j (O.θ' v j x) :=
      congrArg (fun u => w j (O.θ' v j u)) ((y v j).symm_apply_apply x)
    have hm : w j (O.e j (O.θ' v j x)) ∈ R.WL F false j :=
      (hZ j _).1 (hT.2.le (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩))
    have := goodOp_classSum_base hOk hG hHV hjV hHW hU hB j (R.mu v) hθ (y v j x) (by rw [e, ← he]; exact hm)
    rw [e, ← he] at this
    exact this
  refine ⟨w, fun j => coord_lattice j (hZ j) (hM j), fun v hv j =>
    ⟨key v j (hrat v hv j) ((hI v hv).1 j) ((hT v hv).1 j).2.1, ?_⟩⟩
  have := key (conjPl v) j (by rw [hμ v]; exact hrat v hv j) ((hI v hv).2 j) ((hT v hv).2 j).2.1
  rwa [hμ v] at this

end Tied

section Free

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

end Free

end GlobalTheory.BigOnBase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd → SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) dd χ (diagCols (Fin b)) omd → ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (p₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = (_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) p₀ → ∀ (t : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * (t : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd p φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag | exact GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag | (intros; apply GlobalTheory.ThetaSiegelRat.thetaSum_omd_of_fix_diag <;> assumption)
end

