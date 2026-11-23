module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIota
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCoordSqSumLeHilbertSchmidtUnitaryGroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

private theorem hs_eq_ipL (X : Matrix (Fin n) (Fin n) ℂ) : hs X = ipL X X := by
  rw [ipL_apply]
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem hs_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem hs_mul_le (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by

  have key : ∀ i j, ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := by
    intro i j
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  simp only [Formalism.REAL.hs, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖B k j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ j, ∑ k, ‖B k j‖ ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by congr 1; exact Finset.sum_comm

private theorem hs_neg' (X : Matrix (Fin n) (Fin n) ℂ) : hs (-X) = hs X := by
  simp only [Formalism.REAL.hs, Matrix.neg_apply, norm_neg]

private theorem hs_inv_eq (X : Matrix (Fin n) (Fin n) ℂ) : hs (Jm ε * Xᴴ * Jm ε) = hs X := by

  have hsign : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := by
    intro a; split_ifs <;> simp
  simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, norm_mul, norm_star, hsign, one_mul, mul_one]
  exact Finset.sum_comm

private theorem hs_sub_add_hs_add_eq_parallelogram (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hs (X - Y) + hs (X + Y) = 2 * hs X + 2 * hs Y := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := parallelogram_law_with_norm ℝ (X i j) (Y i j)
  rw [sq, sq, sq, sq]
  linarith

theorem sum_coord_sq_le_hs_and_hs_le (n d : ℕ) (ε : Fin n → Bool) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i)) (g : UJ ε)
    (hsp : (uMat g - 1) - Jm ε * (uMat g - 1)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E)) :
    ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 ≤ hs (uMat g - 1) ∧
      hs (uMat g - 1) ≤ ∑ i, (((uMat g - 1) * (E i)ᴴ).trace).re ^ 2 + hs (uMat g - 1) ^ 2 / 4 := by
  set X := uMat g - 1 with hXdef
  set Y := Jm ε * Xᴴ * Jm ε with hYdef

  have hc : ∀ i, ipL (E i) (X - Y) = 2 * ((X * (E i)ᴴ).trace).re := by
    intro i
    rw [ipL_sub_inv (hG i) X, ipL_apply]
  have hexp : X - Y = ∑ i, ipL (E i) (X - Y) • E i := eq_sum_of_mem_span hE hsp

  have hD : hs (X - Y) = 4 * ∑ i, ((X * (E i)ᴴ).trace).re ^ 2 := by
    have h1 : ipL (X - Y) (X - Y) = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) := by
      calc ipL (X - Y) (X - Y) = ipL (X - Y) (∑ i, ipL (E i) (X - Y) • E i) :=
            congrArg (fun Z => ipL (X - Y) Z) hexp
        _ = ∑ i, ipL (E i) (X - Y) * ipL (X - Y) (E i) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            simp only [map_smul, smul_eq_mul]
        _ = ∑ i, ipL (E i) (X - Y) * ipL (E i) (X - Y) :=
            Finset.sum_congr rfl fun i _ => by rw [ipL_comm (E i) (X - Y)]
    rw [hs_eq_ipL, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc i]; ring

  have hS : hs (X + Y) ≤ hs X ^ 2 := by
    have hYX : X + Y = -(Y * X) := add_inv_eq g
    have hYn : hs Y = hs X := hs_inv_eq X
    rw [hYX, hs_neg', sq]
    calc hs (Y * X) ≤ hs Y * hs X := hs_mul_le Y X
      _ = hs X * hs X := by rw [hYn]
  have hpara := hs_sub_add_hs_add_eq_parallelogram X Y
  have hYn : hs Y = hs X := hs_inv_eq X
  have hnn : 0 ≤ hs (X + Y) := hs_nonneg' _
  constructor <;> linarith

end GlobalTheory.NilCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TripOfTerms
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.TermPair
open GlobalTheory.ModIdent GlobalTheory.DegAsm.AdaptInv
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

theorem perp_lift [FiniteDimensional K V] {F G : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (hU : IsUnimod H Λ) (h : IsAdm G F Λ (g : 𝓞 K)) {l : V} (hl : l ∈ Λ) (hp : ∀ x ∈ G.X, H.B x l = 0) :
    ∃ m ∈ Λ, l - (g : K) • m ∈ perp H F.X := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) F.X), IsIntegral ℤ ((g : K)⁻¹ * H.B x l) := by
    rintro ⟨x, hxΛ, hxS⟩
    obtain ⟨x', -, h1, h2⟩ := h (Fin.last r) 0 x hxΛ (by
      rw [zero_smul, sub_zero]; exact hxS)
    obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 h2
    rw [zero_smul, sub_zero] at h1
    have a1 := hp x' h1
    have a5 : H.B (x' - x) l = g * H.B n l := by rw [hxn]; simp
    obtain ⟨c, hc⟩ := integral_of_unimod hU hn hl
    have : (g : K)⁻¹ * H.B x l = ((-c : 𝓞 K) : K) := by
      rw [inv_mul_eq_iff_eq_mul₀ hg0]
      change _ = (g : K) * (-(c : K))
      rw [hc]
      simp only [map_sub, LinearMap.sub_apply] at a5
      linear_combination a1 - a5
    show IsIntegral ℤ ((g : K)⁻¹ * H.B x l)
    rw [this]
    exact (-c).isIntegral_coe
  let φ : ↥(Λ ⊓ rs (𝓞 K) F.X) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨(g : K)⁻¹ * H.B x l, hdiv x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B ((a : V) + b) l = (g : K)⁻¹ * H.B a l + (g : K)⁻¹ * H.B b l
        simp [mul_add]
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B (a • (b : V)) l = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l)
        rw [← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨m, hm, hφ⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU F.X φ
  refine ⟨m, hm, (mem_perp_iff H _ _).2 fun u hu => orth_symm ?_⟩
  have hΛ := (isLatMod_top_bot_iff Λ).1 hU.1
  have hfull : Submodule.IsFullLattice K Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg K hΛ.1, span_eq_top := hΛ.2 }
  obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem (K := K) hfull u
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hs' : algebraMap (𝓞 K) K s • u ∈ Λ := by rw [algebraMap_smul]; exact hs
  have e : H.B (algebraMap (𝓞 K) K s • u) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • u) l :=
    hφ ⟨_, hs', F.X.smul_mem _ hu⟩
  rw [eq_inv_mul_iff_mul_eq₀ hg0] at e
  apply mul_left_cancel₀ hs0
  simp only [map_sub, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
    smul_eq_mul] at e ⊢
  linear_combination -e

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_X_iff {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hγ : ∀ a, G.e a = γ (F.e a)) (x : V) :
    γ x ∈ G.X ↔ x ∈ F.X := by
  have : G.X = F.X.map (γ : V →ₗ[K] V) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [hγ]
    rfl
  rw [this, Submodule.mem_map_equiv]
  simp

omit [NumberField K] [StarRing K] in
theorem mem_smul_iff (γ : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) : γ x ∈ γ • Λ ↔ x ∈ Λ := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := γ.injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩


omit [NumberField K] in
theorem mem_graph {F G : FlagD H r} {HW : HermSpace K W} {e : W →ₗ[K] V} (he : IsEmb F HW e)
    (hI : ∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X)
    (hlift : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0)
    {γ : V ≃ₗ[K] V} {h : W ≃ₗ[K] W} (hγ : ∀ a, G.e a = γ (F.e a)) (hh : IsH F G e γ h) (g : ℕ)
    (Λ' : Submodule (𝓞 K) V) (w v : W) :
    (h w, v) ∈ (datOf F G e g (γ • Λ')).2 ↔
      ∃ x ∈ Λ', ∃ m ∈ γ • Λ', e w - x ∈ F.X ∧ e v - (γ x + (g : K) • m) ∈ F.X := by
  obtain ⟨y, hy, hy1, hy2⟩ := hh w
  have hy' : ∀ u ∈ V0 F G, H.B y u = 0 := (mem_perp_iff H _ _).1 hy
  constructor
  · intro hm
    have hm' : (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X) := hm
    obtain ⟨⟨a, b⟩, hab, ⟨s, t⟩, ⟨hs, ht⟩, hst⟩ := Submodule.mem_sup.1 hm'
    obtain ⟨e1, e2⟩ := Prod.mk.inj hst
    have hs : s ∈ F.X := hs
    have ht : t ∈ F.X := ht
    obtain ⟨ha, -, l, hl, m, hm, h1, h2⟩ := (mem_iota F G _ g a b).1 hab
    have ha' := ((mem_perp_lattice_flag_iff G F _ a).1 ha).1
    rw [jointSpan_comm] at ha'
    have k1 : y - a ∈ G.X := by
      refine hI _ ?_ fun u hu => by simp [hy' u hu, ha' u hu]
      have := F.X.add_mem hy1 hs
      rw [← e1] at this
      convert this using 1; abel
    refine ⟨γ.symm l, by rw [← mem_smul_iff γ]; simpa using hl, m, hm, ?_, ?_⟩
    · rw [← mem_X_iff hγ, map_sub, LinearEquiv.apply_symm_apply]
      have := G.X.sub_mem (G.X.add_mem k1 h1) hy2
      convert this using 1; abel
    · rw [LinearEquiv.apply_symm_apply, ← e2]
      have := F.X.add_mem h2 ht
      convert this using 1; abel
  · rintro ⟨x, hx, m, hm, h1, h2⟩
    have hx' := (mem_smul_iff γ Λ' x).2 hx
    obtain ⟨s, hs, hb⟩ := hlift (e v) ((he.2 _).2 (Submodule.mem_sup_left ⟨v, rfl⟩))
    have k1 : y - γ x ∈ G.X := by
      have := G.X.add_mem hy2 ((mem_X_iff hγ _).2 h1)
      rw [map_sub] at this
      convert this using 1; abel
    have k2 : e v - s - (γ x + (g : K) • m) ∈ F.X := by
      have := F.X.sub_mem h2 hs
      convert this using 1; abel
    show (e (h w), e v) ∈ iotaGraph F G (γ • Λ') (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)
    refine Submodule.mem_sup.2 ⟨(y, e v - s), (mem_iota F G _ g _ _).2 ⟨?_, ?_, γ x, hx', m, hm, k1, k2⟩,
      (-(y - e (h w)), s), ⟨F.X.neg_mem hy1, hs⟩, by simp⟩
    · exact (mem_perp_lattice_flag_iff G F _ _).2 ⟨by rw [jointSpan_comm]; exact hy', _, hx', k1⟩
    · exact (mem_perp_lattice_flag_iff F G _ _).2 ⟨fun u hu => orth_symm (hb u hu), _,
        Submodule.add_mem _ hx' (gsmul_mem g hm), k2⟩

theorem geom [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {F G : FlagD H r} {𝔡 : Ideal (𝓞 K)} {N : NF H r}
    (hN : Adapt F G 𝔡 N) :
    (∀ v ∈ F.X, (∀ w ∈ V0 F G, H.B v w = 0) → v ∈ G.X) ∧
    (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F G, H.B v (w - x) = 0) := by
  obtain ⟨-, h, h'⟩ := hN
  obtain ⟨-, -, -, h1, -, -, -, hl, -⟩ := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1
  rw [sitesCommonSpace_v0_eq_Vp h h'] at h1 hl
  rw [x_eq h] at hl
  refine ⟨fun v hv hw => ?_, fun w hw => hl w fun a => ?_⟩
  · have := ((h1 v (isotropicSpan_le_jointSpan_left F G hv)).1 hw).2
    rwa [x_eq h'] at this
  · have k : N.F.e a - F.e a ∈ F.X := xa_mono F (Nat.le_of_lt_succ a.2) (h a)
    have := orth_of_mem_X F (fun b => hw b.castSucc) k
    rw [map_sub, LinearMap.sub_apply, hw a, sub_zero] at this
    exact this

end GlobalTheory.DegAsm.TermPair

namespace GlobalTheory.DegAsm
open GlobalTheory.ModIdent TermPair

theorem trip_of_terms : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N N' : NF H r) (g : ℕ) (Λ Λ' : Submodule (𝓞 K) V) (γ γ' : V ≃ₗ[K] V) (h h' : W ≃ₗ[K] W), 1 ≤ g → IsEmb F HW e → Adapt F G 𝔡 N → Adapt F G' 𝔡 N' → N.IsTerm g Λ → N'.IsTerm g Λ → γ ∈ isomGrp H → γ' ∈ isomGrp H → (∀ a, G.e a = γ (F.e a) ∧ G'.e a = γ' (F.e a)) → γ • Λ' = Λ → γ' • Λ' = Λ → IsH F G e γ h → IsH F G' e γ' h' → (∀ x ∈ Λ ⊓ rs (𝓞 K) (perp H F.X), γ' (γ.symm x) - x ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)) → (datOf F G e g Λ, datOf F G' e g Λ, h * h'⁻¹) ∈ Trip HW g (lat0 F e Λ) r (N.gI g Λ) (N'.gI g Λ) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N N' g Λ Λ' γ γ' h h' hg he hN hN' hT hT' hγ hγ' hE
    hΛ hΛ' hh hh' hβ
  obtain ⟨k, hk, -, hku, hkl⟩ := _root_.GlobalTheory.DegAsm.exists_isH K V W H HW e hK r F G 𝔡 N γ he hN hγ fun a => (hE a).1
  obtain ⟨k', hk', -, hku', hkl'⟩ := _root_.GlobalTheory.DegAsm.exists_isH K V W H HW e hK r F G' 𝔡 N' γ' he hN' hγ' fun a => (hE a).2
  obtain rfl := hku h hh
  obtain rfl := hku' h' hh'
  have d1 := hkl g Λ'
  have d2 := hkl' g Λ'
  rw [hΛ] at d1
  rw [hΛ'] at d2
  obtain ⟨⟨hU, hF, hG⟩, hA⟩ :=
    ((adapt_invariants K V H hK r F G 𝔡 N hN).2.2.2.2.2.2.2.2 g Λ).1.1 hT
  have hA' : IsAdm G F Λ (g : 𝓞 K) := by
    refine isAdm_symm (fun a => ?_) hA
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [hF.2, hG.2]
    · rw [hF.1, hG.1]
  have key : ∀ w : W, ∀ x ∈ Λ', e w - x ∈ F.X → ∃ n ∈ Λ, γ' x - γ x - (g : K) • n ∈ F.X := by
    intro w x hx hw
    have hxΛ : γ x ∈ Λ := hΛ ▸ (mem_smul_iff γ Λ' x).2 hx
    have hp : ∀ u ∈ G.X, H.B u (γ x) = 0 := by
      intro u hu
      obtain ⟨u, rfl⟩ := γ.surjective u
      rw [mem_X_iff fun a => (hE a).1] at hu
      rw [(mem_isomGrp H γ).1 hγ]
      have a1 := X_iso F hu hw
      have a2 := orth_of_mem_X F (fun b => (he.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) b.castSucc) hu
      rw [map_sub, a2] at a1
      simpa using a1
    obtain ⟨m, hm, hmp⟩ := perp_lift hg hU hA' hxΛ hp
    obtain ⟨s, hs, t, ⟨-, ht⟩, hst⟩ := Submodule.mem_sup.1 (hβ _ ⟨Λ.sub_mem hxΛ (gsmul_mem g hm), hmp⟩)
    obtain ⟨n, hn, rfl⟩ := (mem_smulLat g Λ s).1 hs
    have hm' : γ' (γ.symm m) ∈ Λ := by
      rw [← hΛ', mem_smul_iff, ← mem_smul_iff γ, hΛ]
      simpa using hm
    refine ⟨n + γ' (γ.symm m) - m, Λ.sub_mem (Λ.add_mem hn hm') hm, ?_⟩
    have ht : t ∈ F.X := ht
    convert ht using 1
    simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply] at hst
    rw [smul_sub, smul_add, eq_sub_of_add_eq' hst]
    abel
  refine ⟨(_root_.GlobalTheory.DegAsm.isDat_datOf K V W H HW e hK r F G 𝔡 N g Λ hg he hN hT).1,
    (_root_.GlobalTheory.DegAsm.isDat_datOf K V W H HW e hK r F G' 𝔡 N' g Λ hg he hN' hT').1, mul_mem hk (inv_mem hk'), ?_, fun y v => ?_⟩
  · show imLat (h * h'⁻¹) (datOf F G' e g Λ).1 = (datOf F G e g Λ).1
    rw [d1, d2]
    unfold imLat
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
  · obtain ⟨w, rfl⟩ := h'.surjective y
    have e1 := mem_graph he (geom hK hN).1 (geom hK hN).2 (fun a => (hE a).1) hh g Λ' w v
    have e2 := mem_graph he (geom hK hN').1 (geom hK hN').2 (fun a => (hE a).2) hh' g Λ' w v
    rw [hΛ] at e1
    rw [hΛ'] at e2
    have e3 : (h * h'⁻¹) (h' w) = h w := by simp
    show (h' w, v) ∈ (datOf F G' e g Λ).2 ↔ ((h * h'⁻¹) (h' w), v) ∈ (datOf F G e g Λ).2
    rw [e3, e1, e2]
    constructor
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m + n, Λ.add_mem hm hn, h1, ?_⟩
      have := F.X.add_mem h2 h3
      convert this using 1
      rw [smul_add]; abel
    · rintro ⟨x, hx, m, hm, h1, h2⟩
      obtain ⟨n, hn, h3⟩ := key w x hx h1
      refine ⟨x, hx, m - n, Λ.sub_mem hm hn, h1, ?_⟩
      have := F.X.sub_mem h2 h3
      convert this using 1
      rw [smul_sub]; abel

end GlobalTheory.DegAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThree
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem vol_gram_codim_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  intro k j _ hjk m hm P hP0
  have hP : k - 2 ≤ Module.finrank ℂ P := by omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : d + 2 - 2 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 3 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 2 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (measure_mono fun B hB => ?_)
      (le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_))
    · exact ⟨hB.1, hB.2.2⟩
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have h2 : M ^ (2 * j ^ 2) ≤ 4 * M ^ (2 * j ^ 2 + 2 * j) := by
      have h3 : M ^ (2 * j ^ 2) ≤ M ^ (2 * j ^ 2 + 2 * j) := pow_le_pow_right₀ hM (Nat.le_add_right _ _)
      have h4 : 0 ≤ M ^ (2 * j ^ 2 + 2 * j) := by positivity
      linarith
    calc _ = (Real.pi * M ^ 2) ^ (3 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (3 * j) * (4 * M ^ (2 * j ^ 2 + 2 * j)) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = _ := by
          rw [← pow_mul (Real.exp 1 / s), mul_comm s j, ← mul_pow, mul_div_assoc, mul_assoc _ (4 : ℝ)]

end GlobalTheory.Amp.GramVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeProductOverGradingLayers
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.LayerBox

theorem pres_uncurry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) volume volume := by
  have hm : Measurable (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b))) := by
    ext y; simp [Set.mem_pi]
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp [volume_pi_pi]

theorem pres_layers (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (h : ι → ∀ i, deg i < m) :
    MeasurePreserving (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) volume volume := by
  have hm : Measurable (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun c => Set.univ.pi (fun v => Set.univ.pi (fun i => s (v, i.1)))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Prod.forall]
    constructor
    · rintro H ⟨c, hc⟩ v ⟨i, hi⟩
      simp only at hi
      subst hi
      exact H v i
    · intro H v i
      exact H ⟨deg i, h v i⟩ v ⟨i, rfl⟩
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp only [volume_pi_pi]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun i => (⟨deg i, h v i⟩ : Fin m))]
  refine Finset.prod_congr rfl fun c _ => ?_
  symm
  apply Finset.prod_subtype (f := fun i => volume (s (v, i)))
  intro i
  simp [Fin.ext_iff]

theorem volume_layer_box : ∀ (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (ι → ∀ i, deg i < m) → (∀ c, MeasurableSet (D c)) → volume {x : ι → Fin d → ℝ | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} = ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ d m deg D h hD
  let F : Set (ι × Fin d → ℝ) :=
    {z | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ∈ D c}
  have hF : MeasurableSet F := by
    have : F = ⋂ c, ⋂ (_ : c < m),
        (fun (z : ι × Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ⁻¹' D c := by
      ext z; simp [F]
    rw [this]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (hD c).preimage (by fun_prop)
  have h1 := (pres_uncurry ι (Fin d)).measure_preimage hF.nullMeasurableSet
  have h2 := (pres_layers ι d m deg h).measure_preimage hF.nullMeasurableSet
  have key : ∀ (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (c : ℕ) (hc : c < m),
      (fun v (i : {i : Fin d // deg i = c}) => y ⟨deg i.1, h v i.1⟩ v ⟨i.1, rfl⟩) = y ⟨c, hc⟩ := by
    intro y c hc
    funext v i
    obtain ⟨i, hi⟩ := i
    subst hi
    rfl
  have h3 : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' F = Set.univ.pi (fun c : Fin m => D c) := by
    ext y
    simp only [F, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro H c
      have := H c c.2
      rwa [key y c c.2] at this
    · intro H c hc
      rw [key y c hc]
      exact H ⟨c, hc⟩
  rw [h3, volume_pi_pi, Fin.prod_univ_eq_prod_range (fun c => volume (D c))] at h2
  rw [h2, ← h1]
  rfl

end GlobalTheory.LayerBox
end

