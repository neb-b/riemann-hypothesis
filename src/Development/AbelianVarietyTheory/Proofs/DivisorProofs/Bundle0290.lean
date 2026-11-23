module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhat
section
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM

namespace GlobalTheory.OmAStab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] (χ : G →* H) (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set G) ∈ 𝓝 g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem continuous_invT_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => (invT h).val :=
  (Units.continuous_coe_inv (M := Matrix D D k)).matrix_transpose

theorem continuous_invT_inv_val {D : Type} [Fintype D] [DecidableEq D] :
    Continuous fun h : GL D k => ((invT h)⁻¹).val :=
  (Units.continuous_val (M := Matrix D D k)).matrix_transpose

theorem isLocallyConstant_comp_invT {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    {Φ : Matrix A D k → ℂ} (hΦ : Φ ∈ SB (Matrix A D k)) :
    IsLocallyConstant fun h : GL D k => fun X : Matrix A D k => Φ (X * (invT h).val) := by
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
  set M : GL D k → Matrix D D k := fun h => (invT h).val with hM
  set N : GL D k → Matrix D D k := fun h => ((invT h)⁻¹).val with hN
  have hMc : Continuous M := continuous_invT_val
  have hNc : Continuous N := continuous_invT_inv_val
  have hMN : ∀ h, M h * N h = 1 := fun h => Units.mul_inv (invT h)
  have hNM : ∀ h, N h * M h = 1 := fun h => Units.inv_mul (invT h)
  have hq : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * M p.1) :=
    hl.comp_continuous (continuous_snd.matrix_mul (hMc.comp continuous_fst))
  have hr : IsLocallyConstant fun p : GL D k × Matrix A D k => Φ (p.2 * N p.1 * M h0) :=
    hl.comp_continuous ((continuous_snd.matrix_mul (hNc.comp continuous_fst)).matrix_mul continuous_const)
  have hK1 : IsCompact ((fun Y => Y * N h0) '' tsupport Φ) :=
    hK.isCompact.image (continuous_id.matrix_mul continuous_const)
  have htend : ∀ X : Matrix A D k, Filter.Tendsto (fun p : GL D k × Matrix A D k => (h0, p.2))
      (𝓝 (h0, X)) (𝓝 (h0, X)) := fun X => (continuous_const.prodMk continuous_snd).tendsto' _ _ rfl
  have e1 : ∀ᶠ h in 𝓝 h0, ∀ X ∈ (fun Y => Y * N h0) '' tsupport Φ, Φ (X * M h) = Φ (X * M h0) := by
    refine hK1.eventually_forall_of_forall_eventually fun X _ => ?_
    have a1 := hq.eventually_eq (h0, X)
    have a2 := (htend X).eventually (hq.eventually_eq (h0, X))
    filter_upwards [a1, a2] with p hp1 hp2
    exact hp1.trans hp2.symm
  have e2 : ∀ᶠ h in 𝓝 h0, ∀ Y ∈ tsupport Φ, Φ (Y * N h * M h0) = Φ Y := by
    refine hK.isCompact.eventually_forall_of_forall_eventually fun Y _ => ?_
    have a2 := (continuous_snd.tendsto (h0, Y)).eventually (hl.eventually_eq Y)
    filter_upwards [hr.eventually_eq (h0, Y), a2] with p hp hp2
    refine hp.trans (Eq.trans ?_ hp2.symm)
    show Φ (Y * N h0 * M h0) = Φ Y
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  filter_upwards [e1, e2] with h h1 h2
  funext X
  show Φ (X * M h) = Φ (X * M h0)
  by_cases hA : X * M h0 ∈ tsupport Φ
  · exact h1 X ⟨X * M h0, hA, by simp only [Matrix.mul_assoc, hMN, Matrix.mul_one]⟩
  by_cases hB : X * M h ∈ tsupport Φ
  · have := h2 _ hB
    rw [Matrix.mul_assoc X, hMN, Matrix.mul_one] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

theorem isOpen_omA_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  intro k _ _ _ _ a d ν β hβ Φ hΦ
  have hb : IsLocallyConstant fun h : GL (Fin d) k => β (gdet h) :=
    (isLocallyConstant_of_isOpen_ker β hβ).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hn : IsLocallyConstant fun h : GL (Fin d) k => GlobalTheory.SplitWeil.nabs k (gdet h) :=
    (GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det
  have hc : IsLocallyConstant fun h : GL (Fin d) k => omA ν β 1 h Φ := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun h0 => ?_
    filter_upwards [hb.eventually_eq h0, hn.eventually_eq h0,
      (isLocallyConstant_comp_invT hΦ).eventually_eq h0] with h e1 e2 e3
    funext X
    have e4 := congrFun e3 X
    simp only [omA, apow, inv_one, Units.val_one, Matrix.one_mul, e1, e2, e4]
  exact hc.isOpen_fiber Φ

end GlobalTheory.OmAStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitWeil.FourierPi (box isCompact_box exists_box_subset)
open scoped Topology

noncomputable section

namespace GlobalTheory.KSp

theorem mem_box_of_forall_dot {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {d : Type} [Fintype d] [DecidableEq d] (ψ : AddChar F ℂ) {t₀ : Fˣ}
    (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F} (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) :
    v ∈ box d (t₀ * s⁻¹) := by
  intro i _
  by_contra h
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le] at h
  have hw : v i ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at h
    exact absurd h (not_lt_of_ge zero_le')
  apply ht
  have hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      have e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j := by
        push_cast
        field_simp
      have hpos : 0 < valuation F (v j) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hw
      rw [e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]
      exact mul_le_mul' h.le le_rfl
    · simp [Pi.single_eq_of_ne hj, GlobalTheory.SplitWeil.cball]
  have h2 := hv _ hu
  rwa [single_dotProduct, div_mul_cancel₀ _ hw] at h2

theorem isPair_addChar_form : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  intro F _ _ _ _ _ V _ _ _ _ _ ψ hψ hn h1 β hs hnd
  haveI := GlobalTheory.WeilM.nonarch_field F
  haveI := IsModuleTopology.toContinuousAdd F V
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ)
  let T : Fˣ := Units.mk0 t ht0
  have hT : ψ (T : F) ≠ 1 := ht
  let b := Module.finBasis F V
  let e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F) := LinearMap.pi fun i => β (b i)
  have hf₂ : Function.Injective f₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd y
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]
  have hbij : Function.Bijective f₂ :=
    ⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩
  let e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := LinearEquiv.ofBijective f₂ hbij
  have key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y := by
    intro u y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]
  have cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm := fun g =>
    ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap,
      IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩
  have ann : ∀ (s : Fˣ) y, (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) →
      e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹) := by
    intro s y h
    exact mem_box_of_forall_dot ψ hT s fun u hu => by rw [← key]; exact h u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    rw [map_add (f := _), LinearMap.add_apply, AddChar.map_add_eq_mul]
  · intro x y
    rw [hs]
  · intro x y
    exact hn _
  · exact (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · intro U hU
    have hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨r, hr⟩ := exists_box_subset hU'
    refine ⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹), (isCompact_box _).image (cont e₁).2,
      fun y hy => ?_⟩
    have h2 := ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩
    rw [show T * (T * r⁻¹)⁻¹ = r by rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]] at h2
    simpa using hr h2
  · intro U hU
    have hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨s, hs'⟩ := exists_box_subset hU'
    exact ⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2,
      fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩

end GlobalTheory.KSp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel
open scoped NNReal

namespace GlobalTheory.LGrp.SatakeCompare

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem isSubquotient_smInd_congr {G V W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {H H' : Subgroup G} (h : H = H') (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H), σ ⟨g, hg⟩ = σ' ⟨g, h ▸ hg⟩) (π : Representation ℂ G V) :
    _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H σ) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.PRep.smInd H' σ') := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g g.2
  rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem blk_points (n : Type) (j : n) :
    _root_.GlobalTheory.SmGL.blk (_root_.GlobalTheory.SmGL.points n) j = j := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_Q_eq_parab_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).Q =
      _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  simp only [_root_.GlobalTheory.SmGL.mem_parab, blk_points]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_p_apply_eq_diag (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) (i : n) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).p q i : kˣ) : k) = (q : GL n k) i i := rfl

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem leviProj_points_eq_leviTorus_borel_p (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q)
    (hq : (q : GL n k) ∈ _root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points n)) :
    _root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points n) ⟨q, hq⟩ =
      _root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q) := by
  funext a
  ext i j
  rw [_root_.GlobalTheory.SmGL.leviProj_apply]
  cases i; cases j
  simp [_root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points, borelGL_p_apply_eq_diag]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem modulus_leviEmb_eq_smGL_modulus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [(a : α) → Fintype (m a)] [(a : α) → DecidableEq (m a)] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) (U : Subgroup (GL n k))
    (hU : U = _root_.GlobalTheory.SmGL.unipRad k e) (hc : IsClosed (U : Set (GL n k)))
    (g : _root_.GlobalTheory.SmGL.Levi k m) (x : Subgroup.normalizer (U : Set (GL n k)))
    (hx : (x : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g) :
    ((_root_.GlobalTheory.LGrp.modulus U hc x : NNReal) : ℝ) = _root_.GlobalTheory.SmGL.modulus k m g := by
  obtain ⟨x, hg⟩ := x
  simp only at hx
  subst hx
  subst hU
  letI : MeasurableSpace (_root_.GlobalTheory.SmGL.unipRad k e) := borel _
  haveI : BorelSpace (_root_.GlobalTheory.SmGL.unipRad k e) := ⟨rfl⟩
  haveI : LocallyCompactSpace (_root_.GlobalTheory.SmGL.unipRad k e) :=
    hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (_root_.GlobalTheory.SmGL.unipRad k e) := Measure.haar
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    inferInstance
  have hK : MeasurableSet (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)) :=
    K.isCompact.isClosed.measurableSet
  have h1 := _root_.GlobalTheory.LGrp.modulus_measure _ hc μ ⟨_, hg⟩ (K : Set _)
  have h2 := _root_.GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul k α n m e μ g _ hK
  have hset : (_root_.GlobalTheory.LGrp.conjAut (_root_.GlobalTheory.SmGL.unipRad k e) ⟨_, hg⟩) '' (K : Set _) =
      {u : _root_.GlobalTheory.SmGL.unipRad k e | ∃ s ∈ (K : Set (_root_.GlobalTheory.SmGL.unipRad k e)),
        (u : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e g * (s : GL n k) *
          (_root_.GlobalTheory.SmGL.leviEmb k e g)⁻¹} := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, _root_.GlobalTheory.LGrp.conjAut_coe _ _ _⟩
    · rintro ⟨s, hs, hu⟩
      exact ⟨s, hs, Subtype.ext ((_root_.GlobalTheory.LGrp.conjAut_coe _ _ _).trans hu.symm)⟩
  rw [hset, h2] at h1
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h3 := (ENNReal.mul_left_inj hpos hfin).1 h1
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact ((ENNReal.ofReal_eq_ofReal_iff (_root_.GlobalTheory.SmGL.modulus_pos k g).le
    (NNReal.coe_nonneg _)).1 h3).symm

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_U_eq_unipRad_points (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] :
    (_root_.GlobalTheory.LGrp.borelGL k n).U = _root_.GlobalTheory.SmGL.unipRad k (_root_.GlobalTheory.SmGL.points n) := by
  ext g
  rw [_root_.GlobalTheory.LGrp.LeviDatum.mem_U,
    _root_.GlobalTheory.SmGL.mem_unipRad, ← borelGL_Q_eq_parab_points]
  constructor
  · rintro ⟨hQ, hp⟩
    refine ⟨hQ, fun a i j => ?_⟩
    have h := congrArg (fun u : kˣ => (u : k)) (congrFun hp a)
    simp only [borelGL_p_apply_eq_diag, Pi.one_apply, Units.val_one] at h
    cases i; cases j
    simpa using h
  · rintro ⟨hQ, hd⟩
    refine ⟨hQ, funext fun a => Units.ext ?_⟩
    rw [borelGL_p_apply_eq_diag]
    simpa using hd a () ()

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_s_eq_leviEmb_points_leviTorus (k : Type) [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (t : n → kˣ) :
    (_root_.GlobalTheory.LGrp.borelGL k n).s t =
      _root_.GlobalTheory.SmGL.leviEmb k (_root_.GlobalTheory.SmGL.points n)
        (_root_.GlobalTheory.SmGL.leviTorus k n t) := by
  ext i j
  change ((_root_.GlobalTheory.LGrp.diagHom k n t : GL n k) : Matrix n n k) i j = _
  rw [_root_.GlobalTheory.LGrp.diagHom_val]
  simp [_root_.GlobalTheory.SmGL.leviEmb, _root_.GlobalTheory.SmGL.leviTorus, _root_.GlobalTheory.SmGL.points]
  by_cases h : i = j <;> simp [h]

open MeasureTheory ValuativeRel in
open scoped NNReal in
private theorem borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] (q : (_root_.GlobalTheory.LGrp.borelGL k n).Q) :
    (((_root_.GlobalTheory.LGrp.borelGL k n).deltaHalf q : ℂˣ) : ℂ) =
      ((_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : n => Unit)
        (_root_.GlobalTheory.SmGL.leviTorus k n ((_root_.GlobalTheory.LGrp.borelGL k n).p q)) : ℂˣ) : ℂ) := by
  rw [_root_.GlobalTheory.LGrp.LeviDatum.deltaHalf_coe, _root_.GlobalTheory.SmGL.val_deltaHalf,
    _root_.GlobalTheory.LGrp.LeviDatum.delta_apply,
    modulus_leviEmb_eq_smGL_modulus k (_root_.GlobalTheory.SmGL.points n) _
      (borelGL_U_eq_unipRad_points k n) _ _ _ (borelGL_s_eq_leviEmb_points_leviTorus k n _)]


open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem _root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (α : n → ℂˣ) :
    _root_.GlobalTheory.LGrp.IsSubquot π (_root_.GlobalTheory.LGrp.psGL k α) ↔
      _root_.GlobalTheory.SmGL.IsSubquotient π
        (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar k (α i)) := by
  change _root_.GlobalTheory.SmGL.IsSubquotient π (_root_.GlobalTheory.LGrp.psGL k α) ↔ _
  unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd _root_.GlobalTheory.LGrp.LeviDatum.nIndQ
  unfold _root_.GlobalTheory.SmGL.prinSeries _root_.GlobalTheory.SmGL.indB _root_.GlobalTheory.SmGL.parInd
  refine isSubquotient_smInd_congr (borelGL_Q_eq_parab_points k n) _ _ (fun g hg => ?_) π
  refine LinearMap.ext fun z => ?_
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.LGrp.twist_apply,
    _root_.GlobalTheory.LGrp.charRep_apply, _root_.GlobalTheory.SmGL.twist_apply,
    _root_.GlobalTheory.SmGL.ofChar_apply]
  rw [leviProj_points_eq_leviTorus_borel_p k n ⟨g, hg⟩, borelGL_deltaHalf_eq_smGL_deltaHalf_leviTorus]
  simp [_root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.LGrp.unrTorus_apply,
    _root_.GlobalTheory.LGrp.unrChar_eq]


open MeasureTheory ValuativeRel in
open scoped NNReal in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] in
theorem _root_.GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n V : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (S : Multiset ℂˣ), _root_.GlobalTheory.LGrp.HasSatakeGL π S ↔
      ∃ α : n → ℂˣ, Finset.univ.val.map α = S ∧ _root_.GlobalTheory.SmGL.HasSatake π α := by
  intro k _ _ _ _ n V _ _ _ _ _ π S
  unfold _root_.GlobalTheory.LGrp.HasSatakeGL _root_.GlobalTheory.LGrp.InUPSGL _root_.GlobalTheory.SmGL.HasSatake
    _root_.GlobalTheory.SmGL.IsSpherical _root_.GlobalTheory.LGrp.IsIrrSmooth
  rw [_root_.GlobalTheory.LGrp.isSpherical_iff]
  constructor
  · rintro ⟨⟨α, hα, ⟨-, hirr⟩, hsub⟩, hsph⟩
    exact ⟨α, hα, hirr, hsph, (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).1 hsub⟩
  · rintro ⟨α, hα, hirr, hsph, hsub⟩
    have hsub' := (_root_.GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff k n π α).2 hsub
    refine ⟨⟨α, hα, ⟨?_, hirr⟩, hsub'⟩, hsph⟩
    refine _root_.GlobalTheory.SmGL.IsSubquotient.isSmooth hsub' ?_
    unfold _root_.GlobalTheory.LGrp.psGL _root_.GlobalTheory.LGrp.LeviDatum.nInd
    exact _root_.GlobalTheory.LGrp.LeviDatum.nInd_isSmooth _ _

end GlobalTheory.LGrp.SatakeCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaxPrincipleWeightedFiniteTypeInt
section
open scoped TensorProduct

namespace GlobalTheory

theorem isLocalization_rat_tensor (B : Type) [CommRing B] :
    letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B);
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)) (ℚ ⊗[ℤ] B) :=
  IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)

theorem intMap_le_nonZeroDivisors (B : Type) [CommRing B] [IsDomain B] [CharZero B] :
    Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ) ≤ nonZeroDivisors B := by
  rintro _ ⟨n, hn, rfl⟩
  have h : n ≠ 0 := nonZeroDivisors.ne_zero hn
  exact mem_nonZeroDivisors_of_ne_zero (by simpa using h)

noncomputable def ratExtPoint {B : Type} [CommRing B] (x : B →+* ℂ) : ℚ ⊗[ℤ] B →+* ℂ :=
  (Algebra.TensorProduct.lift (algebraMap ℚ ℂ).toIntAlgHom x.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem ratExtPoint_tmul {B : Type} [CommRing B] (x : B →+* ℂ) (q : ℚ) (b : B) :
    ratExtPoint x (q ⊗ₜ[ℤ] b) = (q : ℂ) * x b := by
  simp [ratExtPoint]

theorem local_max_principle_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  intro B _ _ _ _
  letI tB : TopologicalSpace (B →+* ℂ) :=
    TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance
  intro ψ hψ s hs x₀ δ hδ
  letI := Algebra.TensorProduct.rightAlgebra (R := ℤ) (A := ℚ) (B := B)
  haveI := isLocalization_rat_tensor B
  have hle := intMap_le_nonZeroDivisors B
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors (ℚ ⊗[ℤ] B) hle
  have hinj : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hle
  set φ : B →+* ℚ ⊗[ℤ] B := algebraMap B (ℚ ⊗[ℤ] B) with hφ
  have hφ' : ∀ b, φ b = (1 : ℚ) ⊗ₜ[ℤ] b := fun _ => rfl
  obtain ⟨d, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg ℚ (ℚ ⊗[ℤ] B)
  letI : Algebra (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℚ) (ℚ ⊗[ℤ] B) := hfin
  letI tB' : TopologicalSpace (ℚ ⊗[ℤ] B →+* ℂ) :=
    TopologicalSpace.induced (fun x : ℚ ⊗[ℤ] B →+* ℂ => (x : ℚ ⊗[ℤ] B → ℂ)) inferInstance
  have hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hev' : ∀ b : ℚ ⊗[ℤ] B, Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x b := fun b =>
    (continuous_apply b).comp continuous_induced_dom
  have hres : Continuous fun x : ℚ ⊗[ℤ] B →+* ℂ => x.comp φ :=
    continuous_induced_rng.2 (continuous_pi fun b => hev' (φ b))
  have hext : Continuous fun x : B →+* ℂ => ratExtPoint x := by
    refine continuous_induced_rng.2 (continuous_pi fun t => ?_)
    change Continuous fun x : B →+* ℂ => ratExtPoint x t
    induction t using TensorProduct.induction_on with
    | zero => simpa using continuous_const
    | tmul q b => simp only [ratExtPoint_tmul]; exact continuous_const.mul (hev b)
    | add t u ht hu => simp only [map_add (f := _)]; exact ht.add hu
  have hcomp : ∀ x : B →+* ℂ, (ratExtPoint x).comp φ = x := fun x => by
    ext b
    simp [hφ', ratExtPoint_tmul]
  obtain ⟨W, K, hW, hK, hKs, hb⟩ := GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial d (ℚ ⊗[ℤ] B) hg (fun x => ψ (x.comp φ))
    (hψ.comp hres) (φ s) (fun h => hs (hinj (h.trans (map_zero _).symm))) (ratExtPoint x₀) δ hδ
  refine ⟨(fun x => ratExtPoint x) ⁻¹' W, (fun x => x.comp φ) '' K,
    hext.continuousAt.preimage_mem_nhds hW, hK.image hres, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hKs x hx
  · intro N f R hR y hy
    have h := hb N (φ f) R (fun x hx => hR _ ⟨x, hx, rfl⟩) (ratExtPoint y) hy
    have h2 : ratExtPoint y (φ f) = y f := by rw [← RingHom.comp_apply, hcomp]
    simpa only [hcomp, h2] using h

end GlobalTheory
end

