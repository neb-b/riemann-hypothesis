module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Formalism.LocalToGlobal.Columns.LevGCount
public import Formalism.HermitianLattices.FinalMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Formalism.MainNotions Formalism.L2.Col
open scoped TensorProduct

namespace GlobalTheory.Mem.DuInt

theorem idx_eq (g k : ℕ) (hg : g.Prime) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.idxColLoc g k ∧ Nat.card (GL (Fin k) (ZMod g)) = g ^ (k * (k - 1) / 2) * n := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have h1 : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (HU (ZMod g) k) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ⟨fun h => ?_, fun h => isUpperUni_of_mem_uniUT le_rfl h⟩)
    have : A ∈ uSet (ZMod g) (fun i j : Fin k => i < j) :=
      ⟨h.2, fun i j hne hij => h.1 i j (lt_of_le_of_ne (not_lt.1 hij) hne.symm)⟩
    rw [← uniUT_full_eq] at this
    exact this
  have h2 := (HU (ZMod g) k).card_mul_index
  have h3 := card_HU (ZMod g) k
  rw [Nat.card_zmod] at h3
  refine ⟨(HU (ZMod g) k).index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_, by rw [← h2, h3]⟩
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  rw [h1, ← h2]
  have h4 : (0 : ℝ) < Nat.card (HU (ZMod g) k) := by exact_mod_cast Nat.card_pos
  push_cast
  field_simp

theorem dimV_nat {R : Ranks} (P : HCParam R) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((P.u i : ℚ) : ℝ) := by
  have hk : 0 < R.k := by have := R.m_add_three_le_k; omega
  have hanti : StrictAnti P.u := by
    have key : ∀ d : ℕ, ∀ (a : ℕ) (h : a + d + 1 < R.k), P.u ⟨a + d + 1, h⟩ < P.u ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => intro a h; exact (P.v_gt_u ⟨a, by omega⟩).trans (P.u_gt_v ⟨a, by omega⟩)
      | succ d ih =>
        intro a h
        exact ((P.v_gt_u ⟨a + d + 1, by omega⟩).trans (P.u_gt_v ⟨a + d + 1, by omega⟩)).trans (ih a (by omega))
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < b from hab)
    exact key d a hb
  choose z hz using P.u_half
  have gen : ∀ (N : ℕ) (_ : 0 < N) (u : Fin N → ℚ) (z : Fin N → ℤ), StrictAnti u → (∀ i, u i = z i + 1 / 2) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((u i : ℚ) : ℝ) := by
    intro N hN u z hu hz
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    obtain ⟨c, hc⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => - z i)
    have e1 : StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) = ((Matrix.vandermonde fun i => - z i).det : ℤ) := by
      rw [Matrix.det_vandermonde]
      unfold StandardLattice.vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => Finset.prod_congr (by ext; simp) fun b _ => ?_
      rw [hz a, hz b]
      push_cast
      ring
    have e2 : StandardLattice.facProd (M + 1) = (M.superFactorial : ℕ) := by
      unfold StandardLattice.facProd
      rw [← Nat.prod_range_succ_factorial]
      push_cast
      rfl
    have h3 : (0 : ℝ) < (M.superFactorial : ℕ) := by
      rw [← e2]
      exact Finset.prod_pos fun i _ => by positivity
    have h4 : 0 < StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) := by
      refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
      have := hu (Finset.mem_filter.1 hb).2
      have : ((u b : ℚ) : ℝ) < u a := by exact_mod_cast this
      linarith
    have e5 : StandardLattice.dimV (fun i => ((u i : ℚ) : ℝ)) = c := by
      unfold StandardLattice.dimV
      rw [e1, e2, hc]
      push_cast
      field_simp
    have h6 : (0 : ℝ) < c := by
      rw [← e5]
      exact div_pos h4 (e2 ▸ h3)
    have h7 : 0 < c := by exact_mod_cast h6
    refine ⟨c.toNat, by omega, ?_⟩
    rw [e5]
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg h7.le)
  exact gen R.k hk P.u z hanti hz

section Lat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def resHom (N : Submodule (𝓞 E) V) : autLat (E := E) N →* Module.End (𝓞 E) N where
  toFun γ := ((γ.1 : V →ₗ[E] V).restrictScalars (𝓞 E)).restrict fun _ hx => autLat_apply γ.2 hx
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem finrank_red (N : Submodule (𝓞 E) V) (hN : Submodule.IsFullLattice E N) (w : Ideal (𝓞 E)) [w.IsMaximal] :
    Module.finrank (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) = Module.finrank E V := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN.toIsLattice))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  have : Module.Flat (𝓞 E) N := inferInstance
  have hr : Module.finrank (𝓞 E) N = Module.finrank E V := by
    have : IsLocalizedModule (nonZeroDivisors (𝓞 E)) N.subtype := by
      refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
      · have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) V E
        exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (LinearMap.id : V →ₗ[𝓞 E] V) s
      · have hy : y ∈ Submodule.span E (N : Set V) := (Submodule.IsFullLattice.span_eq_top (self := hN)) ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
    rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) N.subtype le_rfl,
      IsFractionRing.finrank_right_eq (𝓞 E) E V]
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := 𝓞 E) (M := N) (S := 𝓞 E ⧸ w) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr] at h1
  exact h1

theorem card_dvd_card_GL (N : Submodule (𝓞 E) V) (hN : Submodule.IsFullLattice E N) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) (Γ : Subgroup (V ≃ₗ[E] V)) [Finite Γ] (hΓ : Γ ≤ autLat N) :
    Nat.card Γ ∣ Nat.card (GL (Fin (Module.finrank E V)) (ZMod g)) := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN.toIsLattice))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 E ⧸ w) = g := by rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype (𝓞 E ⧸ w) := Fintype.ofFinite _
  haveI : NeZero g := ⟨hg.ne_zero⟩
  let e : ZMod g ≃+* 𝓞 E ⧸ w := ZMod.ringEquivOfPrime _ hg (by rw [← hc, Nat.card_eq_fintype_card])
  let b := Module.finBasisOfFinrankEq (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) (finrank_red N hN w)
  let φ : Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) ≃*
      Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) (ZMod g) :=
    (LinearMap.toMatrixAlgEquiv b).toMulEquiv.trans e.symm.mapMatrix.toMulEquiv
  let ρ : Γ →* Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) :=
    ((Module.End.baseChangeHom (𝓞 E) (𝓞 E ⧸ w) N : _ →* _).comp (resHom N)).comp (Subgroup.inclusion hΓ)
  refine Subgroup.card_dvd_of_injective (φ.toMonoidHom.comp ρ).toHomUnits ?_
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have h1 : ρ γ = 1 := φ.injective (by rw [map_one]; exact congrArg Units.val hγ)
  refine Subtype.ext (stab0 hw.ne_top hN.fg (Submodule.IsFullLattice.span_eq_top (self := hN)) hg hgw hbig ⟨hΓ γ.2, 1, fun x hx => ?_⟩
    (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite γ)))
  have h2 : (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (resHom N ⟨γ.1, hΓ γ.2⟩ ⟨x, hx⟩) = (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N) :=
    LinearMap.congr_fun h1 ((1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N))
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul N w) h2
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.eq] at h3
  have h4 := Submodule.mem_map_of_mem (f := N.subtype) h3
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h4
  rw [pow_one]
  exact h4

open Formalism.HermitianLatticesTheory in
theorem mass_mul_idx [StarRing E] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    (L : Submodule (𝓞 E) V) (hL : Submodule.IsFullLattice E L) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
  obtain ⟨⟨s, hs₀⟩, hm, hp⟩ := final_massBasic E V h hs hpos L (by infer_instance)
  obtain ⟨m, hm0, hm1, hm2⟩ := idx_eq g (Module.finrank E V) hg
  have key : ∀ M ∈ s, ((m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) = ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ * m := by
    intro M hM
    have hMl : Submodule.IsFullLattice E M := (hs₀.1 M hM).1
    have hfin := autFinite E V h hs hpos M (by infer_instance)
    have : Finite (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := hfin.to_subtype
    have e : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := rfl
    have h1 := card_dvd_card_GL M hMl w hg hgw hn hbig (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M) inf_le_right
    have h2 : (Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V))).Coprime g := by
      rw [Nat.coprime_comm, hg.coprime_iff_not_dvd]
      intro hd
      have := prime_le_of_dvd_card _ hg hd
      omega
    rw [hm2] at h1
    have h3 := (h2.pow_right _).dvd_of_dvd_mul_left h1
    rw [e, Nat.cast_div h3 (by exact_mod_cast Nat.card_pos.ne'), div_eq_inv_mul]
  have e : ((∑ M ∈ s, m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
    rw [hm s hs₀, ← hm1, Finset.sum_mul, Nat.cast_sum]
    exact Finset.sum_congr rfl key
  refine ⟨_, ?_, e⟩
  have : (0 : ℝ) < Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) :=
    mul_pos hp (by rw [← hm1]; exact_mod_cast hm0)
  rw [← e] at this
  exact_mod_cast this

end Lat

theorem duStarOf_nat : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (hc : Tau R → HCParam R), (∀ i, H.g i % (H.QS * H.q * H.d) = 1) → (∀ i, 2 * R.f * R.k < H.g i - 1) → ∃ n : ℕ, 0 < n ∧ (n : ℝ) = duStarOf H hc := by
  intro R H hc hmod hbig
  letI := H.cmStar
  have hg := H.g_prime 0
  have hdeg : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have hdeg' : Module.finrank ℚ H.E = 2 * R.f := by
    rw [hdeg, show R.f = 2 * R.ord from rfl]; ring
  have hs : SplitsC H.E (H.g 0) := by
    refine splitsC_of_modEq_one R H _ hg ?_
    have := Nat.mod_modEq (H.g 0) (H.QS * H.q * H.d)
    rw [hmod 0] at this
    exact this.symm
  obtain ⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 H.E) | ((H.g 0 : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [show Set.ncard _ = _ from hs]; exact Module.finrank_pos.ne')
  have hn := (splitsC_main R H _ hg hs v hv).1
  haveI := v.isMaximal
  haveI := H.isCMField_hostE
  have hconj : ∀ (φ : H.E →+* ℂ) (x : H.E), φ (star x) = starRingEnd ℂ (φ x) := fun φ x =>
    IsCMField.complexEmbedding_complexConj H.E φ x
  have hsym : (StandardLattice.stdForm H.E R.k).IsSymm := by
    refine LinearMap.isSymm_def.mpr fun x y => ?_
    show starRingEnd H.E (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, starRingEnd_apply, star_mul, star_star]
  have hpos : ∀ x : Fin R.k → H.E, x ≠ 0 → 0 < Algebra.trace ℚ H.E (StandardLattice.stdForm H.E R.k x x) := fun x hx => by
    have := hStd_trace_pos hconj x hx
    rw [hStd_apply] at this
    exact this
  have hL : Submodule.IsFullLattice H.E (StandardLattice.stdLat H.E R.k) := by
    refine { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _)),
             span_eq_top := ?_ }
    have hb : (fun i : Fin R.k => (Pi.single i 1 : Fin R.k → H.E)) = Pi.basisFun H.E (Fin R.k) :=
      funext fun i => (Pi.basisFun_apply H.E (Fin R.k) i).symm
    rw [StandardLattice.stdLat, Submodule.span_span_of_tower, hb, Module.Basis.span_eq]
  obtain ⟨n₁, p₁, e₁⟩ := mass_mul_idx _ hsym hpos _ hL v.asIdeal hg hv hn
    (by rw [Module.finrank_fin_fun, hdeg']; have := hbig 0; omega)
  rw [Module.finrank_fin_fun] at e₁
  obtain ⟨n₂, p₂, e₂, -⟩ := idx_eq (H.g 0) R.k hg
  obtain ⟨n₃, p₃, e₃, -⟩ := idx_eq (H.g 1) R.k (H.g_prime 1)
  choose d pd ed using fun τ => dimV_nat (hc τ)
  obtain ⟨f, hf⟩ : ∃ f, R.f = f + 1 := ⟨R.f - 1, by
    have : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
    omega⟩
  refine ⟨n₁ * n₂ ^ f * n₃ ^ R.f * ∏ τ, d τ, ?_, ?_⟩
  · have := Finset.prod_pos (s := Finset.univ) fun τ _ => pd τ
    positivity
  · unfold duStarOf
    push_cast
    simp only [ed]
    rw [e₁, e₂, e₃, hf]
    ring

end GlobalTheory.Mem.DuInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem cwb_val_mem (l : List (lie (Jm ε))) : ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := by
  intro X hX
  obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
  exact Y.2

theorem cwb_isKFin_Dw (h : Std ε σ) {v : H} (hv : IsKFin ε σ v) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    IsKFin ε σ (Dw σ l v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    exact isKFin_dRep n ε H σ h _ (ih hl') X (hl X (by simp))

theorem cwb_dRep_lin (h : Std ε σ) {w : H} (hw : Sm ε σ w) (a : ℝ) {X Y : Mx n} (hX : X ∈ lieSet ε)
    (hY : Y ∈ lieSet ε) : dRep σ (a • X + Y) w = (a : ℂ) • dRep σ X w + dRep σ Y w := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hh : (Formalism.REAL.Jm ε).IsHermitian := GlobalTheory.SmVec.gram_herm (ε := ε) (P := 1) (by simp)
  have hd : (Formalism.REAL.Jm ε).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hG).ne_zero
  exact GlobalTheory.HolDict.LieAct.dRep_lin hh hd h.1 hw a hX hY

theorem cwb_Dw_sub (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x)
    (hy : Sm ε σ y) : Dw σ l x - Dw σ l y = Dw σ l (x - y) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hxy : x - y ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := Submodule.sub_mem _ hx hy
  have e := GlobalTheory.SmVec.word_add hG h.1 hl hy hxy
  have e' : Dw σ l x = GlobalTheory.SmVec.word σ l (y + (x - y)) := by rw [add_sub_cancel]; rfl
  rw [e', e]
  change GlobalTheory.SmVec.word σ l y + GlobalTheory.SmVec.word σ l (x - y) - GlobalTheory.SmVec.word σ l y = GlobalTheory.SmVec.word σ l (x - y)
  abel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : Mx n → (E →L[ℂ] E)}

theorem cwb_mem_Fam (h : Std ε σ) {T₀ : H →ₗ[ℂ] E}
    (hd : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v →
      HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0)
    {v : H} (hv : IsKFin ε σ v) : (fun l : List (lie (Jm ε)) => T₀ (Dw σ (l.map Subtype.val) v)) ∈ Fam ε ρ := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hK : ∀ l : List (lie (Jm ε)), IsKFin ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => cwb_isKFin_Dw h hv (cwb_val_mem l)
  have hS : ∀ l : List (lie (Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => h.2.2.1 _ (hK l)
  have hmem : ∀ X : lie (Jm ε), (X : Mx n) ∈ lieSet ε := fun X => cwb_val_mem [X] _ (by simp)
  unfold Fam
  refine ⟨?_, ?_, ?_⟩
  · intro l X
    exact hd X (hmem X) _ (hK l)
  · intro l₁ l₂ a X Y
    have hc : ((a • X + Y : lie (Jm ε)) : Mx n) = a • (X : Mx n) + (Y : Mx n) := rfl
    simp only [List.map_append, List.map_cons, happ, hcons, hc]
    have hw := hS l₂
    rw [cwb_dRep_lin h hw a (hmem X) (hmem Y)]
    have h1 : dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)
    have h2 : dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)
    have e1 := GlobalTheory.SmVec.word_add hG h.1 (cwb_val_mem l₁) (Submodule.smul_mem _ (a : ℂ) h1) h2
    have e2 := GlobalTheory.SmVec.word_smul hG h.1 (cwb_val_mem l₁) (a : ℂ) h1
    change T₀ (GlobalTheory.SmVec.word σ _ _) = _ • T₀ (GlobalTheory.SmVec.word σ _ _) + T₀ (GlobalTheory.SmVec.word σ _ _)
    rw [e1, e2, map_add (f := _), map_smul]
  · intro l₁ l₂ X Y Z hZ
    simp only [List.map_append, List.map_cons, happ, hcons]
    have hw := hS l₂
    have h1 : dRep σ (X : Mx n) (dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)) (hmem X)
    have h2 : dRep σ (Y : Mx n) (dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)) (hmem Y)
    rw [← map_sub, cwb_Dw_sub h (cwb_val_mem l₁) h1 h2,
      dRep_bracket n ε H σ h _ hw _ (hmem X) _ (hmem Y), ← hZ]

private theorem isKFin_add {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} {v w : H} (hv : IsKFin ε σ v) (hw : IsKFin ε σ w) :
    IsKFin ε σ (v + w) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  obtain ⟨S', hS', hwS, hSK'⟩ := hw
  refine ⟨S ⊔ S', ?_, Submodule.add_mem_sup hvS hwS, ?_⟩
  · haveI := hS
    haveI := hS'
    infer_instance
  · unfold IsKStableOn at hSK hSK' ⊢
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hSK' g hg z hz)

private theorem isKFin_smul {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} (c : ℂ) {v : H} (hv : IsKFin ε σ v) :
    IsKFin ε σ (c • v) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  exact ⟨S, hS, S.smul_mem c hvS, hSK⟩

private theorem isKFin_zero {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} : IsKFin ε σ (0 : H) := by
  refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
  unfold IsKStableOn
  intro g _ x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]
  exact Submodule.zero_mem _

private theorem mem_UJset_of_mem_Kset_iwasawa_decomposition {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hu' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, show kᴴ * k = 1 from hu', Matrix.one_mul]

private theorem dw_apply_sigma_eq_sigma_dw_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {g : Mx n}
    (hg : g ∈ UJset ε) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Dw σ l (σ g w) = σ g (Dw σ (l.map fun X => g⁻¹ * X * g) w) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    have hX : X ∈ lieSet ε := hl X (by simp)
    change dRep σ X (Dw σ l (σ g w)) =
      σ g (dRep σ (g⁻¹ * X * g) (Dw σ (l.map fun X => g⁻¹ * X * g) w))
    rw [ih hl']
    have hs : Dw σ (l.map fun X => g⁻¹ * X * g) w ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := by
      have hl'' : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ GlobalTheory.SmVec.lieG (Formalism.REAL.Jm ε) := by
        intro Y hY
        obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
        exact GlobalTheory.SmVec.conj_mem_lieG hG hg (hl' Z hZ)
      exact GlobalTheory.SmVec.word_mem hG h.1 hl'' hw
    exact GlobalTheory.SmVec.dRep_rep hG h.1 hs hg hX

end SlopeTestRemainingChoices

theorem casselmanWallach_banach : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  intro hCW n ε H _ _ _ σ hσ E _ _ _ ρ hρ T₀ hK hd
  unfold GlobalTheory.Published.CasselmanWallach at hCW
  obtain ⟨hcl, p, π, dπ, hsm, hπ, hdπ, hp0⟩ := GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep n ε E ρ hρ
  haveI : IsUniformAddGroup (Fam ε ρ) := (Fam ε ρ).toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace (Fam ε ρ) := hcl.completeSpace_coe
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hnil : ∀ x : H, Dw σ [] x = x := fun _ => rfl
  let KF : Submodule ℂ H :=
    { carrier := {v | IsKFin ε σ v}
      add_mem' := fun ha hb => isKFin_add ha hb
      zero_mem' := isKFin_zero
      smul_mem' := fun c _ hv => isKFin_smul c hv }
  let J : KF →ₗ[ℂ] Fam ε ρ :=
    { toFun := fun v => ⟨fun l => T₀ (Dw σ (l.map Subtype.val) v.1), cwb_mem_Fam hσ hd v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_add hG hσ.1 (cwb_val_mem l) (hσ.2.2.1 _ v.2) (hσ.2.2.1 _ w.2)
        show T₀ (Dw σ _ (v.1 + w.1)) = T₀ (Dw σ _ v.1) + T₀ (Dw σ _ w.1)
        rw [← map_add (f := _)]
        exact congrArg T₀ e
      map_smul' := fun c v => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_smul hG hσ.1 (cwb_val_mem l) c (hσ.2.2.1 _ v.2)
        show T₀ (Dw σ _ (c • v.1)) = c • T₀ (Dw σ _ v.1)
        rw [← map_smul]
        exact congrArg T₀ e }
  obtain ⟨T₁, hT₁⟩ := LinearMap.exists_extend J
  have hT₁v : ∀ (v : H) (hv : IsKFin ε σ v), T₁ v = J ⟨v, hv⟩ := fun v hv =>
    LinearMap.congr_fun hT₁ ⟨v, hv⟩
  have hJ : ∀ (v : H) (hv : IsKFin ε σ v) (l : List (lie (Jm ε))),
      (J ⟨v, hv⟩).1 l = T₀ (Dw σ (l.map Subtype.val) v) := fun _ _ _ => rfl
  have hGK : IsGKMap ε σ π dπ T₁ := by
    refine ⟨?_, ?_⟩
    · intro k hk v hv
      have hk' : k ∈ UJset ε := mem_UJset_of_mem_Kset_iwasawa_decomposition hk
      have hkv : IsKFin ε σ (σ k v) := by
        obtain ⟨S, hS, hvS, hSK⟩ := hv
        exact ⟨S, hS, hSK k hk v hvS, hSK⟩
      rw [hT₁v _ hkv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [hπ k hk' (J ⟨v, hv⟩) l, hJ, hJ, dw_apply_sigma_eq_sigma_dw_conj hσ hk' _ (cwb_val_mem l) (hσ.2.2.1 _ hv)]
      have hl : (l.map Subtype.val).map (fun X => k⁻¹ * X * k) = (l.map (adInv hk')).map Subtype.val := by
        simp only [List.map_map]
        rfl
      rw [hl, hK k hk _ (cwb_isKFin_Dw hσ hv (cwb_val_mem _))]
    · intro X hX v hv
      have hXv : IsKFin ε σ (dRep σ X v) := isKFin_dRep n ε H σ hσ v hv X hX
      rw [hT₁v _ hXv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [show (dπ X (J ⟨v, hv⟩)).1 l = (J ⟨v, hv⟩).1 (l ++ [⟨X, hX⟩]) from hdπ ⟨X, hX⟩ _ l, hJ, hJ]
      simp only [List.map_append, List.map_cons, List.map_nil, happ, hcons, hnil]
      try rfl
  obtain ⟨T', hT'0, hSG, -⟩ := hCW n ε H σ hσ.1 hσ.2.1 (Fam ε ρ) p π dπ hsm T₁ hGK
  unfold IsSmoothGMap at hSG
  obtain ⟨hTeq, hTbd⟩ := hSG
  refine ⟨(GlobalTheory.TypeSum.SmoothFrechet.ev ρ []).comp T', ?_, ?_, ?_⟩
  · intro v hv
    show (T' v).1 [] = T₀ v
    rw [hT'0 v hv, hT₁v v hv]
    rfl
  · intro g hg w hw
    show (T' (σ g w)).1 [] = ρ g ((T' w).1 [])
    rw [hTeq g hg w hw, hπ g hg (T' w) []]
    rfl
  · obtain ⟨S, C, hS, hSC⟩ := hTbd 0
    exact ⟨S, C, hS, fun w hw => (hp0 (T' w)).trans (hSC w hw)⟩

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLineStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  first | exact @GlobalTheory.FlagBundle.exists_fr_stepSet | exact GlobalTheory.FlagBundle.exists_fr_stepSet | (intros; apply GlobalTheory.FlagBundle.exists_fr_stepSet <;> assumption)
end

