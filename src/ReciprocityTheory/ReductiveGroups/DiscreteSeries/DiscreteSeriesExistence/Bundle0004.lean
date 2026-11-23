module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CvAEquivariantA
section
noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kUJA (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨k, star k, Matrix.mem_unitaryGroup_iff.1 hk.1, Matrix.mem_unitaryGroup_iff'.1 hk.1⟩, by
    show Formalism.REAL.inUJ ε k
    rw [mir_inUJ_iff]
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]⟩

theorem cvA_equivariantA (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (hαK : ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    σ k (cvA ε σ α v) = cvA ε σ α (σ k v) := by
  set κ := kUJA ε hk with hκdef
  have hκ : Formalism.MainNotions.S.umat κ = k := rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun y => (measurePreserving_mul_right ε y).map_eq⟩
  have hmul : ∀ a b : Formalism.REAL.UJ ε,
      σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) :=
    fun a b => hσ.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  set F : Formalism.REAL.UJ ε → H := fun g => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat (g * κ)) v with hF
  have hR : cvA ε σ α (σ k v) = ∫ g, F g ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    congr 1
    funext g
    rw [hF]
    dsimp only
    rw [hmul, ContinuousLinearMap.comp_apply, hκ]
  have hL : σ k (cvA ε σ α v) = ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_cvA hσ hα hαc v)]
    congr 1
    funext g
    have hc : Formalism.MainNotions.S.umat (κ * g * κ⁻¹) = k * Formalism.MainNotions.S.umat g * star k := rfl
    rw [hF]
    dsimp only
    rw [inv_mul_cancel_right, hc, hαK k hk, hmul, ContinuousLinearMap.comp_apply, hκ, map_smul]
  rw [hL, hR]
  calc ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) = ∫ g, F (g * κ⁻¹) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self (fun x => F (x * κ⁻¹)) κ
    _ = ∫ g, F g ∂(Formalism.REAL.muG ε) := integral_mul_right_eq_self F κ⁻¹

theorem map_le_isoA (T : H →ₗ[ℂ] H) (hT : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T v) = T (σ k v))
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    S.map T ≤ sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} := by
  obtain ⟨hfin, hstab, hirr, ⟨w, hwS, hw0, hwt⟩, hdom⟩ := hS
  have hstab0 : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ LinearMap.ker T) := by
    intro g hg v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    exact ⟨hstab g hg v hv.1, by rw [← hT g hg v, hv.2, _root_.map_zero]⟩
  rcases hirr _ inf_le_left hstab0 with h0 | h0
  · have hinj : ∀ x ∈ S, T x = 0 → x = 0 := fun x hx hTx => by
      have hx' : x ∈ S ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hx, LinearMap.mem_ker.2 hTx⟩
      rw [h0] at hx'
      exact (Submodule.mem_bot ℂ).1 hx'
    apply le_sSup
    show Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map T)
    unfold Formalism.MainNotions.S.IsKTypeOf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · haveI : FiniteDimensional ℂ S := hfin
      infer_instance
    · rintro g hg _ ⟨x, hx, rfl⟩
      rw [hT g hg x]
      exact Submodule.mem_map_of_mem (hstab g hg x hx)
    · intro S' hS' hS'st
      have hst : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap T) := by
        intro g hg v hv
        rw [Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
        exact ⟨hstab g hg v hv.1, by rw [← hT g hg v]; exact hS'st g hg _ hv.2⟩
      rcases hirr _ inf_le_left hst with h1 | h1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hS' hy
        have hx' : x ∈ S ⊓ S'.comap T := Submodule.mem_inf.2 ⟨hx, Submodule.mem_comap.2 hy⟩
        rw [h1, Submodule.mem_bot] at hx'
        rw [hx', _root_.map_zero]
        exact Submodule.zero_mem _
      · right
        refine le_antisymm hS' ?_
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ S ⊓ S'.comap T := by rw [h1]; exact hx
        exact Submodule.mem_comap.1 (Submodule.mem_inf.1 hx').2
    · have hTw : T w ≠ 0 := fun h => hw0 (hinj w hwS h)
      refine ⟨T w, Submodule.mem_map_of_mem hwS, hTw, ?_⟩
      intro θ hθ
      rw [hT _ hθ w, hwt θ hθ, _root_.map_smul]
    · rintro μ' _ ⟨x, hx, rfl⟩ hne hwt'
      have hx0 : x ≠ 0 := fun h => hne (by rw [h, _root_.map_zero])
      refine hdom μ' x hx hx0 ?_
      intro θ hθ
      have h1 := hwt' θ hθ
      rw [hT _ hθ x] at h1
      refine sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hstab _ hθ x hx) (Submodule.smul_mem _ _ hx)) ?_)
      rw [_root_.map_sub, h1, _root_.map_smul, sub_self]
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ S ⊓ LinearMap.ker T := by rw [h0]; exact hx
    rw [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx').2]
    exact Submodule.zero_mem _

theorem exists_cvA_idA (hσ : IsURepOn (UJset ε) σ)
    (hadm : ∀ μ : Fin n → ℝ, FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H))
    (W : Submodule ℂ H) (hWf : FiniteDimensional ℂ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ H | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S})
    {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α, AdmA ε U α ∧ ∀ w ∈ W, cvA ε σ α w = w := by
  classical
  let T : ∀ α, AdmA ε U α → H →ₗ[ℂ] H := fun α hα =>
    { toFun := cvA ε σ α
      map_add' := cvA_add_vec hσ hα.1.continuous hα.2.1
      map_smul' := fun c v => cvA_smul_vec α c v }
  have hTK : ∀ α (hα : AdmA ε U α), ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T α hα v) = T α hα (σ k v) :=
    fun α hα k hk v => cvA_equivariantA hσ hα.1.continuous hα.2.1 hα.2.2.2
      (by rw [← mir_Kset_eq]; exact hk) v
  have hWc : IsCompactElement W :=
    (Submodule.fg_iff_compact W).1 (Module.Finite.iff_fg.1 hWf)
  obtain ⟨t, hts, hWt⟩ :=
    (isCompactElement_iff_exists_le_sSup_of_le_sSup W).1 hWc _ hWsum
  let iso : Submodule ℂ H → Submodule ℂ H := fun S =>
    if h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S then sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} else ⊥
  haveI hisoF : ∀ S, FiniteDimensional ℂ (iso S) := by
    intro S
    by_cases h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S
    · have e : iso S = sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} := dif_pos h
      rw [e]
      exact hadm _
    · have e : iso S = ⊥ := dif_neg h
      rw [e]
      infer_instance
  let W2 := t.sup iso
  have hS_le : ∀ S ∈ t, S ≤ iso S ∧ ∀ α (hα : AdmA ε U α), S.map (T α hα) ≤ iso S := by
    intro S hS
    have h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S := hts hS
    simp only [iso, dif_pos h]
    exact ⟨le_sSup h.choose_spec, fun α hα => map_le_isoA (T α hα) (hTK α hα) h.choose_spec⟩
  have hWW2 : W ≤ W2 :=
    hWt.trans (Finset.sup_le fun S hS => (hS_le S hS).1.trans (Finset.le_sup (f := iso) hS))
  have hmapW : ∀ α (hα : AdmA ε U α), ∀ w ∈ W, cvA ε σ α w ∈ W2 := by
    intro α hα w hw
    have : W ≤ W2.comap (T α hα) :=
      hWt.trans (Finset.sup_le fun S hS => Submodule.map_le_iff_le_comap.1
        (((hS_le S hS).2 α hα).trans (Finset.le_sup (f := iso) hS)))
    exact this hw
  let b := Module.finBasis ℂ W
  let bw : Fin (Module.finrank ℂ W) → H := fun i => (b i : H)
  let R : Submodule ℂ (Fin (Module.finrank ℂ W) → W2) :=
    { carrier := {p | ∃ α, AdmA ε U α ∧ ∀ i, cvA ε σ α (bw i) = (p i : H)}
      add_mem' := by
        rintro p q ⟨α, hα, hp⟩ ⟨β, hβ, hq⟩
        exact ⟨α + β, hα.add hβ, fun i => by
          rw [cvA_add_fun hσ hα.1.continuous hα.2.1 hβ.1.continuous hβ.2.1, hp, hq]
          rfl⟩
      zero_mem' := ⟨0, AdmA.zero U, fun i => by rw [cvA_zero_fun]; rfl⟩
      smul_mem' := by
        rintro c p ⟨α, hα, hp⟩
        exact ⟨c • α, hα.smul c, fun i => by rw [cvA_smul_fun, hp]; rfl⟩ }
  have hRc : IsClosed (R : Set (Fin (Module.finrank ℂ W) → W2)) := R.closed_of_finiteDimensional
  let p0 : Fin (Module.finrank ℂ W) → W2 := fun i => ⟨bw i, hWW2 (b i).2⟩
  have hp0 : p0 ∈ closure (R : Set (Fin (Module.finrank ℂ W) → W2)) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨α, hα, hnear⟩ := exists_nearA hσ hU h1 bw (half_pos hη)
    refine ⟨fun i => ⟨cvA ε σ α (bw i), hmapW α hα _ (b i).2⟩, ⟨α, hα, fun i => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hη]
    intro i
    show dist (bw i) (cvA ε σ α (bw i)) < η
    rw [dist_comm, dist_eq_norm]
    linarith [hnear i]
  rw [hRc.closure_eq] at hp0
  obtain ⟨α, hα, hfix⟩ := hp0
  refine ⟨α, hα, ?_⟩
  have hext : (T α hα).comp W.subtype = W.subtype := b.ext fun i => hfix i
  intro w hw
  exact LinearMap.congr_fun hext ⟨w, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothBr
section
noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}

theorem smBr_inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ; simp

theorem smBr_hasDerivAt_ext (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hgJ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))
  exact hcomp.congr_of_eventuallyEq hev

theorem smBr_rdExt (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (smBr_hasDerivAt_ext f F U g X hU hg hgJ hF hfF hX).deriv

theorem smBr_rdBracket (f : Matrix (Fin n) (Fin n) ℂ → E) (X Y g : Matrix (Fin n) (Fin n) ℂ)
    (hf : S7.SmoothOnGV ε f) (hX : inG ε X) (hY : inG ε Y) (hg : inUJ ε g) :
    S7.RdV X (S7.RdV Y f) g - S7.RdV Y (S7.RdV X f) g = S7.RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → S7.RdV Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => smBr_rdExt f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply (Formalism.REAL.mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) Formalism.REAL.withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (Formalism.REAL.mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : S7.RdV X (S7.RdV Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    smBr_rdExt (S7.RdV Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : S7.RdV Y (S7.RdV X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    smBr_rdExt (S7.RdV X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (Formalism.REAL.lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

end Helpers

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smBr_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))

theorem smBr_dS_eq (Z : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dS σ Z w = S7.RdV Z (fun g => σ g w) 1 := by
  simp only [dS, S7.RdV, one_mul]

theorem smBr_orbit (hσ : IsURepOn (UJset ε) σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z)
    {v : H} (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ Z v) = S7.RdV Z (fun g => σ g v) g := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv 1 smBr_inUJ_one
  have hc := smBr_hasDerivAt_ext (fun g => σ g v) F U 1 Z hU h1U smBr_inUJ_one hF hfF hZ
  simp only [one_mul] at hc
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hfun : ((σ g) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) v) =
      fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v := by
    funext t
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t)]
    rfl
  have h3 : HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v)
      (σ g (fderiv ℝ F 1 Z)) 0 := by
    rw [← hfun]; exact h2
  rw [dS, hc.deriv, S7.RdV, h3.deriv]

end Main

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_bracket (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y)
    {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ X (dS σ Y v) - dS σ Y (dS σ X v) = dS σ (X * Y - Y * X) v := by
  have e1 : dS σ X (dS σ Y v) = S7.RdV X (S7.RdV Y (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hY hv hg) hX smBr_inUJ_one
  have e2 : dS σ Y (dS σ X v) = S7.RdV Y (S7.RdV X (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hX hv hg) hY smBr_inUJ_one
  rw [e1, e2, smBr_dS_eq]
  exact smBr_rdBracket _ X Y 1 hv hX hY smBr_inUJ_one

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothRestrict
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isSmoothVecU_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) (x : S) :
    IsSmoothVecU ε (fun g => (S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL : S →L[ℂ] S)) x ↔
      IsSmoothVecU ε σ (x : H) := by
  set P := S.orthogonalProjectionOnto
  have hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w := by
    intro w hw
    have e : P w = ⟨w, hw⟩ := by
      first
        | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)
        | (show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])
    rw [e]
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    have hmem : σ g (x : H) ∈ S := hSG g hg x x.2
    dsimp only at e1 ⊢
    rw [← e1]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hP _ hmem).symm
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    dsimp only at e1 ⊢
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [e1]

end ReciprocityTheory.ChartRestriction.DS
end
end

