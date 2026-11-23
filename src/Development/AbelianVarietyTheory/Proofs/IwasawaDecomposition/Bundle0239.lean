module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Formalism.LocalToGlobal.Columns.CoefColLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.Isom

variable {D : D7}

theorem gelf_tr {V V' : HSp D} (I : IsoMat V V') {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ}
    (hφ : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) : gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) :=
  _root_.GlobalTheory.Mem.Isom.IsoMat.gelf_tr D V V' I θ hθ τ k φ hφ

theorem cusp_tr {V V' : HSp D} (I : IsoMat V V') {φ : GA D V → ℂ} (hφ : IsCuspFun V φ) : IsCuspFun V' (I.tr φ) :=
  _root_.GlobalTheory.Mem.Isom.isCuspFun_tr D V V' I φ hφ

theorem haar_tr {V V' : HSp D} (I : IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL V' S) 𝓕 μ) : ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧
        ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν :=
  _root_.GlobalTheory.Mem.Isom.haar_fd_phi D V V' I S μ 𝓕 hμ h𝓕

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

theorem isAutFun_tr {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V' (I.tr φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨fun γ hγ g => ?_, ?_, h.cont.comp I.continuous_kap_symm⟩
  · unfold tr
    rw [map_mul]
    exact h.left _ (I.symm.kap_mem_GQ hγ) _
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap I.kap.symm.toMonoidHom, hU.preimage I.continuous_kap_symm, fun k hk hf g => ?_⟩
    unfold tr
    rw [map_mul]
    exact e _ hk (I.symm.kap_mem_GfC hf) _

theorem normInf_kap_le (hθ : IsInfFam θ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g :=
  _root_.GlobalTheory.Mem.Isom.normInf_kap_le D V V' I θ hθ

theorem foldr_tr (hθ : IsInfFam θ) (φ : GA D V → ℂ) (l : List (D.what₂.Tau × Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V' p.1) :
    l.foldr (fun p f => Rder θ V' p.1 p.2 f) (I.tr φ) =
      I.tr ((l.map fun p => (p.1, I.symm.adP p.1 p.2)).foldr (fun p f => Rder θ V p.1 p.2 f) φ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      I.Rder_tr hθ (hl p List.mem_cons_self)]

def trLin : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) where
  toFun := I.tr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFunSm_tr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V' (I.tr φ) := by
  have ha := I.isAutFun_tr hφ.toIsAutFun
  refine { left := ha.left, level := ha.level, cont := ha.cont, smooth := I.tr_mem_SmFun hθ hφ.smooth, zfin := ?_, growth := ?_ }
  · obtain ⟨W, hW, m, s⟩ := hφ.zfin
    refine ⟨(W ⊓ GlobalTheory.Mem.AutSpace.SmFun θ V).map I.trLin, inferInstance, ⟨φ, ⟨m, hφ.smooth⟩, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, ⟨s τ k f hf.1, (GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).mem f hf.2⟩, (_root_.GlobalTheory.Mem.Isom.gelf_tr I hθ τ k hf.2).symm⟩
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨c, hc0, hc⟩ := I.symm.normInf_kap_le hθ
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun p => (p.1, I.symm.adP p.1 p.2)) (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact I.symm.adP_mem (hl q hq)) (I.kap.symm x)
    refine ⟨|C| * c ^ N, fun g hg => ?_⟩
    rw [I.foldr_tr hθ φ l hl]
    unfold tr
    rw [map_mul, mul_assoc |C|, ← mul_pow]
    exact (hC _ (I.symm.kap_mem_GinfC hg)).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) (hc g) N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
      (abs_nonneg _))

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [trW] using this

end IsoMat

namespace IsoMat
variable {V V' : HSp D} (I : IsoMat V V')

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : IdC D} {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => I.symm.isThetaFunO_tr S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact I.isThetaFunO_tr S (h.om_pres _ _ (hT f hf))
  · rw [omT_apply, omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := haar_tr I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (I.isThetaFunO_tr S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end IsoMat

theorem exists_isom_transport : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap →
    ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧
      (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧
      ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om →
        ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧
          ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  intro D V V' e he
  let I := IsoMat.ofEquiv e he
  refine ⟨I.kap, I.continuous_kap, I.continuous_kap_symm, fun g => ⟨fun hg => ?_, I.kap_mem_GQ⟩,
    fun θ hθ F hF => ⟨I.isAutFunSm_tr hθ hF.1, cusp_tr I hF.2⟩, fun ψ S χ χ' om hom => ?_⟩
  · have := I.symm.kap_mem_GQ hg
    rwa [← I.kap_symm_apply, I.kap.symm_apply_apply] at this
  · refine ⟨I.omT S om, I.isWeilDatumO_tr S hom, fun f hf => ⟨I.trW S f, I.isThetaFunO_tr S hf, fun hne h0 => hne ?_, fun g h => ?_⟩⟩
    · have := I.trW_symm_trW S f
      rw [h0] at this
      rw [← this]
      rfl
    · show I.trW S (om (g, I.kap.symm (I.kap h)) (I.symm.trW S (I.trW S f))) 0 = om (g, h) f 0
      rw [I.kap.symm_apply_apply, I.trW_symm_trW]
      show om (g, h) f ((I.phi S).symm 0) = om (g, h) f 0
      rw [map_zero]

end GlobalTheory.Mem.Isom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinement
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.StepLift

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

variable {ι : Type} {m k k' : ι → ℕ} {τ : ι} {K : Type} [Field K]

theorem mul_apply_rest {O : Subring K} (g : Mat m K) {h : Mat m K} (hh : Par k O h) (a : Fin (m τ))
    (j : Rest m k τ) : (g * h) τ a j.1 = ∑ l : Rest m k τ, g τ a l.1 * h τ l.1 j.1 := by
  have hz : ∀ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * h τ l.1 j.1 = 0 := by
    intro l
    have hl : ¬ k τ ≤ (l.1 : ℕ) := l.2
    have hj : k τ ≤ (j.1 : ℕ) := j.2
    rw [(hh τ).2.2.2 l.1 j.1 (by omega) (by rw [Fin.lt_def]; omega), mul_zero]
  rw [Pi.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ)),
    Finset.sum_eq_zero (fun l _ => hz l), add_zero]

private theorem det_submatrix_rest_ne_zero {O : Subring K} {g : Mat m K} (hg : Par k O g) (σ : ι) :
    ((g σ).submatrix (Subtype.val : Rest m k σ → Fin (m σ)) (Subtype.val : Rest m k σ → Fin (m σ))).det ≠ 0 := by
  have hd := Matrix.twoBlockTriangular_det (g σ) (fun i : Fin (m σ) => k σ ≤ (i : ℕ)) (by
    intro i hi j hj
    have hi' : ¬ k σ ≤ (i : ℕ) := hi
    have hj' : k σ ≤ (j : ℕ) := hj
    exact (hg σ).2.2.2 i j (by omega) (by rw [Fin.lt_def]; omega))
  intro h0
  apply (hg σ).2.1
  rw [hd]
  exact mul_eq_zero_of_left h0 _

theorem row_ne_zero {h : Mat m K} (hh : Par k ⊤ h) (hk : k τ < m τ) :
    (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := by
  intro h0
  exact det_submatrix_rest_ne_zero hh τ (Matrix.det_eq_zero_of_row_eq_zero ⟨⟨k τ, hk⟩, le_refl _⟩ fun j => congrFun h0 j)

theorem par_succ_iff {h G : Mat m K} (hh : Par k ⊤ h) (hG : Par k ⊤ G) (hk : k τ < m τ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    Par k' ⊤ (h * G⁻¹) ↔ ∃ t : K, ∀ j : Rest m k τ, h τ ⟨k τ, hk⟩ j.1 = t * G τ ⟨k τ, hk⟩ j.1 := by
  have hX : Par k ⊤ (h * G⁻¹) := hh.mul hG.inv
  have hXG : h * G⁻¹ * G = h := by rw [mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
  have hrow : ∀ j : Rest m k τ,
      h τ ⟨k τ, hk⟩ j.1 = ∑ l : Rest m k τ, (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 * G τ l.1 j.1 := by
    intro j
    rw [← mul_apply_rest (h * G⁻¹) hG, hXG]
  constructor
  · intro hP
    refine ⟨(h * G⁻¹) τ ⟨k τ, hk⟩ ⟨k τ, hk⟩, fun j => ?_⟩
    rw [hrow j, Finset.sum_eq_single (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ)]
    · intro l _ hl
      have hl2 : k τ ≤ (l.1 : ℕ) := l.2
      have hl3 : (l.1 : ℕ) ≠ k τ := fun e => hl (Subtype.ext (Fin.ext e))
      have hlt : (⟨k τ, hk⟩ : Fin (m τ)) < l.1 := by rw [Fin.lt_def]; show k τ < (l.1 : ℕ); omega
      rw [(hP τ).2.2.2 ⟨k τ, hk⟩ l.1 (by show k τ < k' τ; omega) hlt, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rintro ⟨t, ht⟩
    have hv : Matrix.vecMul (fun l : Rest m k τ => (h * G⁻¹) τ ⟨k τ, hk⟩ l.1 -
        if l = (⟨⟨k τ, hk⟩, le_refl _⟩ : Rest m k τ) then t else 0)
        ((G τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = 0 := by
      funext j
      have e := hrow j
      rw [ht j] at e
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← e, sub_self]
    have hv0 := Matrix.eq_zero_of_vecMul_eq_zero (det_submatrix_rest_ne_zero hG τ) hv
    intro σ
    refine ⟨fun _ _ => Subring.mem_top _, hX.det_ne σ, Subring.mem_top _, ?_⟩
    intro i j hi hij
    by_cases hσ : σ = τ
    · subst hσ
      by_cases hik : (i : ℕ) < k σ
      · exact (hX σ).2.2.2 i j hik hij
      · have hi' : (i : ℕ) = k σ := by omega
        have hj : k σ ≤ (j : ℕ) := by rw [Fin.lt_def] at hij; omega
        have hne : (⟨j, hj⟩ : Rest m k σ) ≠ ⟨⟨k σ, hk⟩, le_refl _⟩ := by
          intro e
          have e' := congrArg (fun x : Rest m k σ => (x.1 : ℕ)) e
          simp only at e'
          rw [Fin.lt_def] at hij
          omega
        have e := congrFun hv0 ⟨j, hj⟩
        simp only [hne, if_false, sub_zero, Pi.zero_apply] at e
        have hieq : i = ⟨k σ, hk⟩ := Fin.ext hi'
        subst hieq
        exact e
    · exact (hX σ).2.2.2 i j (by rw [← h2 σ hσ]; exact hi) hij

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem row_eq {φ : Ω →ₐ[F] Ω'} {O : Subring Ω} (hk : k τ < m τ) {A₀ A : Mat m Ω} (hA : ∀ τ, (A τ).det ≠ 0)
    (hP : Par k O (A * A₀⁻¹)) (hd : (dualBlock k τ A₀ A).det ≠ 0) {s : Rest m k τ → Ω'} {A' : Mat m Ω'} {a : Ω'}
    (ha : ∀ j : Rest m k τ, (A' * (A₀.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * s j) (j : Rest m k τ) :
    (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 = a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
  have hPφ : Par k ⊤ ((A * A₀⁻¹).map φ) := hP.map (φ : Ω →+* Ω') fun _ _ => Subring.mem_top _
  have hAφ : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ => by
    rw [show (A.map φ σ).det = φ (A σ).det from Mat.det_map A (φ : Ω →+* Ω') σ]
    exact (map_ne_zero φ).2 (hA σ)
  have hmap : (A * A₀⁻¹).map φ = A.map φ * (A₀.map φ)⁻¹ := by
    rw [show (A * A₀⁻¹).map φ = A.map φ * A₀⁻¹.map φ from Mat.map_mul A A₀⁻¹ (φ : Ω →+* Ω'),
      show A₀⁻¹.map φ = (A₀.map φ)⁻¹ from Mat.map_inv A₀ (φ : Ω →+* Ω')]
  have hZ : A' * (A.map φ)⁻¹ * (A * A₀⁻¹).map φ = A' * (A₀.map φ)⁻¹ := by
    rw [hmap, mul_assoc, ← mul_assoc (A.map φ)⁻¹, Mat.inv_mul hAφ, one_mul]
  have hNd := det_submatrix_rest_ne_zero hPφ τ
  have hrow : Matrix.vecMul (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1)
      ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))) = a • s := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← ha j, ← hZ, mul_apply_rest _ hPφ]
    rfl
  have hz : (fun l : Rest m k τ => (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ l.1) =
      a • Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := by
    rw [← Matrix.smul_vecMul, ← hrow, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hNd), Matrix.vecMul_one]
  have hmul : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ))).map φ * (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_submatrix_rest_ne_zero hP τ)),
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hinv : (((A * A₀⁻¹) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹.map φ = ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ := (Matrix.inv_eq_right_inv hmul).symm
  have hfin : Matrix.vecMul s ((((A * A₀⁻¹).map φ) τ).submatrix (Subtype.val : Rest m k τ → Fin (m τ)) (Subtype.val : Rest m k τ → Fin (m τ)))⁻¹ = Matrix.mulVec ((dualBlock k τ A₀ A).map φ) s := by
    rw [← Matrix.mulVec_transpose, ← hinv]
    try rfl
  rw [← hfin]
  exact congrFun hz j

theorem existsUnique_bears (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω)
    (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) (hS : ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z')
    (K : Type) [Field K] (x : Sp K ⟶ M.Z) (A : Mat m Ω) (hA : A ∈ S.S (x (IsLocalRing.closedPoint K)))
    (h : Mat m K) (hh : Par k ⊤ h) : ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  have hB := hE _ A hA
  have hA0P : Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
    (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint hA)
  have hc : (fun j : Rest m k τ => h τ ⟨k τ, hk⟩ j.1) ≠ 0 := row_ne_zero hh hk
  obtain ⟨p, ⟨hpf, hp⟩, huniq⟩ := hP.lifts K x (dualBlock k τ A₀ A) hB.1 hB.2 _ hc
  have key : ∀ q : Sp K ⟶ M'.Z, q ≫ f = x → (Bears S' φ A h q ↔
      ∃ i, M'.Div (((dualBlock k τ A₀ A).map φ).mulVec s) i (q (IsLocalRing.closedPoint K)) ∧
        ∀ j, h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 * M'.val q
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i)) := by
    intro q hqf
    have hfq : f (q (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
      rw [← hqf]
      first | rfl | simp
    have hsp : ∀ w, q w ⤳ q (IsLocalRing.closedPoint K) :=
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton q _)
    have hunit : ∀ y : Ω', y ∈ M'.O (q (IsLocalRing.closedPoint K)) →
        (M'.val q y ≠ 0 ↔ y ≠ 0 ∧ y⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K))) := fun y hy =>
      (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton q _) ⟨y, hy⟩).trans
        (RatModel.isUnit_O_iff _)
    have hstep : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k (M'.O (q (IsLocalRing.closedPoint K))).toSubring (A' * (A.map φ)⁻¹) ∧
        ∃ a : Ω', ∀ j : Rest m k τ, (A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1 =
          a * ((dualBlock k τ A₀ A).map φ).mulVec s j := by
      intro A' hA'
      rw [hS] at hA'
      obtain ⟨hpar, a, ha⟩ := hA'
      exact ⟨hpar A (by rw [hfq]; exact hA), a,
        fun j => row_eq hk (fun σ => Fr.det_ne hA σ) hA0P hB.1 ha j⟩
    have hW : ∀ A' ∈ S'.S (q (IsLocalRing.closedPoint K)),
        Par k ⊤ ((A' * (A.map φ)⁻¹).map (M'.val q)) := fun A' hA' =>
      (hstep A' hA').1.map_of (M'.val q)
        (RatModel.valHom q (q (IsLocalRing.closedPoint K)) (RatModel.range_eq_singleton q _))
        (fun y => (RatModel.valHom_apply _ _ _ y).symm)
    unfold Bears
    constructor
    · rintro ⟨A', hA', hpar⟩
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨t, ht⟩ := (par_succ_iff hh (hW A' hA') hk h1 h2).1 hpar
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have hdiv : ∀ j, ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have e : ((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀ =
            a * ((dualBlock k τ A₀ A).map φ).mulVec s j * (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
          field_simp
        rw [e]
        exact mul_mem (hmem j) hinv0
      refine ⟨j₀, ⟨hv0, hdiv⟩, fun j => ?_⟩
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀ *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s j₀) := by
        field_simp
      rw [ht j, ht j₀]
      show t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1) =
        t * M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j₀.1) * _
      rw [ha j, ha j₀, e2, RatModel.val_mul hsp (hmem j₀) (hdiv j), mul_assoc]
    · rintro ⟨i, ⟨hvi, hdivi⟩, hci⟩
      obtain ⟨A', hA'⟩ := S'.nonempty (q (IsLocalRing.closedPoint K))
      obtain ⟨hX, a, ha⟩ := hstep A' hA'
      have hmem : ∀ j : Rest m k τ, a * ((dualBlock k τ A₀ A).map φ).mulVec s j ∈
          M'.O (q (IsLocalRing.closedPoint K)) := fun j => by
        have hj := (hX τ).1 ⟨k τ, hk⟩ j.1
        rw [ha j] at hj
        exact hj
      obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 (row_ne_zero (hW A' hA') hk)
      have hu : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀) ≠ 0 := by
        rw [← ha j₀]
        exact hj₀
      obtain ⟨hne0, hinv0⟩ := (hunit _ (hmem j₀)).1 hu
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne0
      have hv0 : ((dualBlock k τ A₀ A).map φ).mulVec s j₀ ≠ 0 := right_ne_zero_of_mul hne0
      have e3 : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ =
          ((dualBlock k τ A₀ A).map φ).mulVec s j₀ / ((dualBlock k τ A₀ A).map φ).mulVec s i *
            (a * ((dualBlock k τ A₀ A).map φ).mulVec s j₀)⁻¹ := by
        field_simp
      have hinvi : (a * ((dualBlock k τ A₀ A).map φ).mulVec s i)⁻¹ ∈ M'.O (q (IsLocalRing.closedPoint K)) := by
        rw [e3]
        exact mul_mem (hdivi j₀) hinv0
      have hui : M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) ≠ 0 :=
        (hunit _ (hmem i)).2 ⟨mul_ne_zero ha0 hvi, hinvi⟩
      refine ⟨A', hA', (par_succ_iff hh (hW A' hA') hk h1 h2).2
        ⟨h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i), fun j => ?_⟩⟩
      show h τ ⟨k τ, hk⟩ j.1 = h τ ⟨k τ, hk⟩ i.1 / M'.val q (a * ((dualBlock k τ A₀ A).map φ).mulVec s i) *
        M'.val q ((A' * (A.map φ)⁻¹) τ ⟨k τ, hk⟩ j.1)
      have e2 : a * ((dualBlock k τ A₀ A).map φ).mulVec s j = a * ((dualBlock k τ A₀ A).map φ).mulVec s i *
          (((dualBlock k τ A₀ A).map φ).mulVec s j / ((dualBlock k τ A₀ A).map φ).mulVec s i) := by
        field_simp
      rw [ha j, e2, RatModel.val_mul hsp (hmem i) (hdivi j), hci j, ← mul_assoc, div_mul_cancel₀ _ hui]
  exact ⟨p, ⟨hpf, (key p hpf).2 hp⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).1 hq.2⟩⟩

end GlobalTheory.FlagBundle.StepLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightRepresentationIrreducible
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem Wt.isIrreducible_rep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n),
    W.rep.IsIrreducible := by
  intro E _ _ _ n W
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Formalism.L2.Col.VV_nontrivial ℂ W, fun U hU => ?_⟩
  refine GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => ?_
  obtain ⟨y, hy, hyg⟩ := _root_.GlobalTheory.InfSurj.exists_infU_cAll_eq E n g hg
  have h := hU ⟨y, hy⟩ x hx
  rw [← hyg]
  exact h

end GlobalTheory.DefU
end

