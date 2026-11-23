module

public import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousPair
public import GroundTheory.GlobalFields.TateThesis.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousTo
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real ContDiff

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpA

theorem dense_sch : DenseRange (schwartzToL2 l) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

def ext (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) : L2 l ≃ₗᵢ[ℂ] L2 l :=
  (ContinuousLinearEquiv.unitsEquiv ℂ (Sch l) V).toLinearEquiv.extendOfIsometry
    (schwartzToL2 l).toLinearMap (schwartzToL2 l).toLinearMap dense_sch dense_sch fun f => hn f

theorem ext_sch (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

theorem G_ext {g h : G l} (h1 : pr g = pr h) (h2 : om g = om h) (h3 : omS g = omS h) : g = h :=
  Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext h2 (Units.ext h3)))

theorem continuous_to {X : Type} [TopologicalSpace X] {F : X → G l} (h1 : Continuous fun x => pr (F x))
    (h2 : ∀ f, Continuous fun x => om (F x) f) : Continuous F :=
  continuous_induced_rng.2 (h1.prodMk (continuous_pi h2))

theorem sp_mul {X : Type} [TopologicalSpace X] {a b : X → Sp l} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => a x * b x :=
  continuous_induced_rng.2 ((continuous_subtype_val.comp ha).mul (continuous_subtype_val.comp hb))

theorem sp_inv {X : Type} [TopologicalSpace X] {a : X → Sp l} (ha : Continuous a) :
    Continuous fun x => (a x)⁻¹ := by
  refine continuous_induced_rng.2 ?_
  show Continuous fun x => -Matrix.J l ℝ * ((a x : Mat l))ᵀ * Matrix.J l ℝ
  exact (continuous_const.mul (continuous_subtype_val.comp ha).matrix_transpose).mul continuous_const

theorem om_cont2 : Continuous fun p : G l × L2 l => om p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Continuous fun p : G l × L2 l => ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ :=
    (continuous_snd.sub continuous_const).norm.add (((continuous_om q.2).comp continuous_fst).sub continuous_const).norm
  have h2 := h1.tendsto q
  simp only [sub_self, norm_zero, add_zero] at h2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h2
  calc ‖om p.1 p.2 - om q.1 q.2‖ = ‖(om p.1 p.2 - om p.1 q.2) + (om p.1 q.2 - om q.1 q.2)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖om p.1 p.2 - om p.1 q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := norm_add_le _ _
    _ = ‖p.2 - q.2‖ + ‖om p.1 q.2 - om q.1 q.2‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem om_mul (g h : G l) (f : L2 l) : om (g * h) f = om g (om h f) := by
  rw [map_mul]; rfl

abbrev gs (l : Type) [Fintype l] : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)

theorem fderiv_gs (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(gs l)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * gs l x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(gs l) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem ann_gs : Ann (1 : Sp l).1 (gs l) := fun j => by
  have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec]
  ext x
  rw [SchwartzMap.smul_apply, dRho_single_inr, dRho_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  linear_combination fderiv_gs j x - (2 * π * (x j : ℂ) * gs l x) * I_sq

theorem gs_zero : gs l 0 = 1 := by simp

theorem dd_one : dd (1 : Mat l) = 1 := by
  have h : upperParabolic (1 : Mat l) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]
  rw [dd, h, det_one]

theorem eps_mem : Mem ((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l) :=
  ⟨fun f => by simp, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩

def eps : G l := ⟨((1, LinearIsometryEquiv.neg ℂ, -1) : Amb l), eps_mem⟩

theorem om_eps (f : L2 l) : om (eps : G l) f = -f := rfl

theorem omS_eps (f : Sch l) : omS (eps : G l) f = -f := by
  show (((-1 : (Sch l →L[ℂ] Sch l)ˣ) : Sch l →L[ℂ] Sch l)) f = -f
  simp

theorem pr_eps : pr (eps : G l) = 1 := rfl

theorem eps_ne : (eps : G l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : omS (eps : G l) φ = omS (1 : G l) φ := by rw [h]
  rw [omS_eps, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : Sch l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)

theorem om_of_omS {g : G l} {c : ℂ} (hc : ∀ f, omS g f = c • f) (F : L2 l) : om g F = c • F := by
  refine dense_sch.induction_on (p := fun F => om g F = c • F) F
    (isClosed_eq (om g).continuous (continuous_const_smul c)) fun f => ?_
  rw [om_sch, hc, map_smul]

end MpA

open MpA

theorem mkElt : MkElt l := by
  intro s U hU hI hN
  obtain ⟨V, rfl⟩ := hU
  have hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖ := fun f => hI.norm f
  have hsurj : Function.Surjective ⇑(V : Sch l →L[ℂ] Sch l) := fun f => ⟨V⁻¹.1 f, by
    show (V.1 * V⁻¹.1) f = f
    rw [V.mul_inv]; rfl⟩
  have hI' : Impl (⇑(Matrix.mulVecLin s.1)) (V : Sch l →L[ℂ] Sch l).toLinearMap := hI
  have hd : ∀ w f, V.1 (dRho w f) = dRho (s.1 *ᵥ w) (V.1 f) := fun w f => hI'.dRho hsurj w f
  set u := ext V hn with hu
  have hc : ∀ f, u (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := fun f => ext_sch V hn f
  have hrho : ∀ w F, u (rho w F) = rho (s.1 *ᵥ w) (u F) := fun w F => by
    refine dense_sch.induction_on (p := fun F => u (rho w F) = rho (s.1 *ᵥ w) (u F)) F
      (isClosed_eq (u.continuous.comp (rho w).continuous) ((rho _).continuous.comp u.continuous)) fun f => ?_
    obtain ⟨g, hg⟩ := exists_rho w f
    have hg' := hI.impl w f g hg
    calc u (rho w (schwartzToL2 l f)) = u (schwartzToL2 l g) := by rw [schwartzToL2_apply, schwartzToL2_apply, toLp_rho hg]
      _ = schwartzToL2 l (V.1 g) := hc g
      _ = rho (s.1 *ᵥ w) (schwartzToL2 l (V.1 f)) := by
        rw [schwartzToL2_apply, schwartzToL2_apply]; exact toLp_rho hg'
      _ = rho (s.1 *ᵥ w) (u (schwartzToL2 l f)) := by rw [hc]
  have hm : Mem ((s, u, V) : Amb l) := ⟨hc, hrho, hd, hN⟩
  exact ⟨(⟨((s, u, V) : Amb l), hm⟩ : sub l), rfl, rfl⟩

theorem topG : TopG l := by
  have hm : ContinuousMul (G l) := ⟨continuous_to (by
      simp only [map_mul]
      exact sp_mul (continuous_pr.comp continuous_fst) (continuous_pr.comp continuous_snd)) fun f => by
      simp only [om_mul]
      exact om_cont2.comp (continuous_fst.prodMk ((continuous_om f).comp continuous_snd))⟩
  have hi : ContinuousInv (G l) := ⟨continuous_to (by
      simp only [map_inv]
      exact sp_inv continuous_pr) fun f => by
      refine continuous_iff_continuousAt.2 fun g0 => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨v, hv⟩ : ∃ v, om g0⁻¹ f = v := ⟨_, rfl⟩
      have hv0 : om g0 v = f := by
        rw [← hv, ← om_mul, mul_inv_cancel, map_one]; rfl
      have key : ∀ g : G l, ‖f - om g v‖ = ‖om g⁻¹ f - v‖ := fun g => by
        rw [← LinearIsometryEquiv.norm_map (om g) (om g⁻¹ f - v), map_sub, ← om_mul, mul_inv_cancel, map_one]
        rfl
      have hc : Continuous fun g : G l => ‖f - om g v‖ := (continuous_const.sub (continuous_om v)).norm
      have h0 := hc.tendsto g0
      rw [hv0, sub_self, norm_zero] at h0
      rw [hv]
      exact h0.congr key⟩
  exact { toContinuousMul := hm, toContinuousInv := hi }

theorem ker : Ker l := by
  refine ⟨eps, eps_ne, fun g => ⟨fun hg => ?_, ?_⟩, om_eps⟩
  · have hsurj : Function.Surjective (omS g) := fun f => ⟨omS g⁻¹ f, by
      show (omS g * omS g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl⟩
    have hpg : ((pr g : Sp l) : Mat l) = 1 := by rw [hg]; rfl
    have hI : Impl id (omS g).toLinearMap := by
      refine ⟨fun f => ?_, fun w f k hk => ?_⟩
      · show ‖schwartzToL2 l (omS g f)‖ = ‖schwartzToL2 l f‖
        rw [← om_sch, LinearIsometryEquiv.norm_map]
      · obtain ⟨k', hk'⟩ := exists_rho w (omS g f)
        have e : omS g k = k' := by
          apply injective_toLp 2 volume
          calc (omS g k).toLp 2 volume = om g (k.toLp 2 volume) := (om_sch g k).symm
            _ = om g (rho w (f.toLp 2 volume)) := by rw [toLp_rho hk]
            _ = rho w (om g (f.toLp 2 volume)) := by rw [om_rho, hpg, one_mulVec]
            _ = rho w ((omS g f).toLp 2 volume) := by rw [← schwartzToL2_apply, om_sch]; rfl
            _ = k'.toLp 2 volume := (toLp_rho hk').symm
        show ⇑(omS g k) = rhoFun w (omS g f)
        rw [e, hk']
    obtain ⟨c, hc⟩ := hI.scalar hsurj
    have hc' : ∀ f, omS g f = c • f := hc
    have hn := omS_nrm g 1 (gs l) ann_gs
    have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
    rw [hpg, e1, Matrix.one_mul, dd_one, hc', SchwartzMap.smul_apply, gs_zero] at hn
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hn
    rcases mul_eq_zero.1 hc2 with h | h
    · left
      have hc1 : c = 1 := sub_eq_zero.1 h
      refine G_ext (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, one_smul, map_one]; rfl
      · rw [hc', hc1, one_smul, map_one]; rfl
    · right
      have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
      refine G_ext (by rw [hg, pr_eps]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, om_eps, neg_one_smul]
      · rw [hc', hc1, omS_eps, neg_one_smul]
  · rintro (rfl | rfl)
    · exact map_one _
    · exact pr_eps

end PositivityTheory.ThKR.Mp

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.MapOfRealMul
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace C

theorem upperPart_mul (s s' : Mat l) :
    upperParabolic (s * s') = s.toBlocks₁₁.map Complex.ofReal * upperParabolic s' + s.toBlocks₁₂.map Complex.ofReal * loQ s' := by
  ext a b
  have e : ∀ x y : ℂ, x * (I * y) = I * (x * y) := fun x y => mul_left_comm x I y
  simp only [upperParabolic, loQ, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub,
    Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]
  ring

theorem map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

theorem det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

theorem dd_mul_eq (s s' : Mat l) (hd : s.toBlocks₁₁.det ≠ 0) :
    dd (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (upperParabolic s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * loQ s').det := by
  have hu : IsUnit s.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hB : s.toBlocks₁₂.map Complex.ofReal =
      s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal := by
    rw [← map_ofReal_mul, hAS]
  rw [dd, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]

theorem blocks_symm {A B C D : Matrix l l ℝ} (h : fromBlocks A B C D * Matrix.J l ℝ * (fromBlocks A B C D)ᵀ = Matrix.J l ℝ) :
    B * Aᵀ = A * Bᵀ := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h1
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1
  exact add_neg_eq_zero.1 h1

theorem isSymm_inv_mul (s : Sp l) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).IsSymm := by
  have hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ := by
    have h := SymplecticGroup.mem_iff.1 s.2
    rw [← fromBlocks_toBlocks s.1] at h
    exact blocks_symm h
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hut : IsUnit s.1.toBlocks₁₁ᵀ.det := by rw [det_transpose]; exact hu
  show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂
  rw [transpose_mul, transpose_nonsing_inv]
  calc s.1.toBlocks₁₂ᵀ * (s.1.toBlocks₁₁ᵀ)⁻¹
      = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]
    _ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]

theorem sympl_sp (s : Sp l) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem sec_apply_zero (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by
  simp only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply,
    dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]

end C

open C

theorem secEx_of (h1 : MkElt l) (h2 : NrmUp l) : SecEx l := by
  intro s hd
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  let uA : (Eu l →L[ℝ] Eu l)ˣ :=
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹,
      by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩
  have hA : IsUnit (bl Sum.inl Sum.inl s.1) := ⟨uA, rfl⟩
  have hinv : Ring.inverse (bl Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹ :=
    Ring.inverse_unit uA
  have hAiB : Ring.inverse (bl Sum.inl Sum.inl s.1) * bl Sum.inl Sum.inr s.1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by
    rw [hinv, map_mul]
    rfl
  have hdA : (bl Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det := det_bl _ _ _
  have hdet : (Ring.inverse (bl Sum.inl Sum.inl s.1)).det * (bl Sum.inl Sum.inl s.1).det = 1 := by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)
    simpa [ContinuousLinearMap.det] using this
  set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef
  have hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc : c ^ 2 = |(Ring.inverse (bl Sum.inl Sum.inl s.1)).det| := by
    rw [hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'
  obtain ⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧
      (0 < s.1.toBlocks₁₁.det → z = 1) := by
    by_cases hpos : 0 < s.1.toBlocks₁₁.det
    · have e : c ^ 2 * s.1.toBlocks₁₁.det = 1 := by
        rw [hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
      refine ⟨1, by simp, ?_, fun _ => rfl⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e]
      simp
    · have hneg : s.1.toBlocks₁₁.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hd
      have e : c ^ 2 * s.1.toBlocks₁₁.det = -1 := by
        rw [hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      refine ⟨I, by simp, ?_, fun h => absurd h hpos⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e, I_sq]
      push_cast
      ring
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
  have hU : IsUnit (z • sec s.1) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 z hz0).map _).mul (isUnit_big hA.ringInverse _ _ hc0)
  have hiso := iso_big hA.ringInverse (bl Sum.inl Sum.inr s.1) (bl Sum.inr Sum.inl s.1) hc
  have hI : Impl (fun w => s.1 *ᵥ w) (z • sec s.1).toLinearMap := by
    refine ⟨fun f => ?_, fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z⟩
    show ‖schwartzToL2 l ((z • sec s.1) f)‖ = ‖schwartzToL2 l f‖
    rw [ContinuousLinearMap.smul_apply, map_smul, norm_smul, hz1, one_mul]
    exact hiso f
  have hN : Nrm s.1 (z • sec s.1) := by
    intro s' f hf
    have key := h2 _ (isSymm_inv_mul s hd) s' f hf
    have ev : (z • sec s.1) f 0 = z * ((c : ℂ) *
        fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) := by
      rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]
    rw [ev, dd_mul_eq s.1 s'.1 hd, ← key]
    calc _ = (z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ))) *
          ((fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) ^ 2 *
            (upperParabolic s'.1 + (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).map Complex.ofReal * loQ s'.1).det) := by ring
      _ = _ := by rw [hz, one_mul]
  obtain ⟨g, hg1, hg2⟩ := h1 s _ hU hI hN
  exact ⟨g, z, hg1, hg2, hzpos⟩

namespace C

def lo (t : ℝ) : Mat l := fromBlocks 1 0 (t • 1) 1

theorem lo_mem (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem lo_mul (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by
  rw [lo, lo, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_mul_lo (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp

theorem exists_det_ne (s : Mat l) (h : dd s ≠ 0) : ∃ t : ℝ, (s.toBlocks₁₁ + t • s.toBlocks₁₂).det ≠ 0 := by
  let M : Matrix l l (Polynomial ℝ) := Matrix.of fun a b =>
    Polynomial.C (s (.inl a) (.inl b)) + Polynomial.X * Polynomial.C (s (.inl a) (.inr b))
  have hev : ∀ t : ℝ, Polynomial.eval t M.det = (s.toBlocks₁₁ + t • s.toBlocks₁₂).det := fun t => by
    have e : Polynomial.eval t M.det = ((Polynomial.evalRingHom t).mapMatrix M).det :=
      RingHom.map_det (Polynomial.evalRingHom t) M
    rw [e]
    congr 1
    ext a b
    simp [M, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]
    ring
  have hev' : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = dd s := by
    have e : Polynomial.eval₂ Complex.ofRealHom (-I) M.det =
        ((Polynomial.eval₂RingHom Complex.ofRealHom (-I)).mapMatrix M).det :=
      RingHom.map_det (Polynomial.eval₂RingHom Complex.ofRealHom (-I)) M
    rw [e, dd]
    congr 1
    ext a b
    simp [M, upperParabolic]
    ring
  have hP : M.det ≠ 0 := fun h0 => h (by rw [← hev', h0, Polynomial.eval₂_zero])
  by_contra hall
  push Not at hall
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono ?_ (Set.infinite_univ (α := ℝ))
  intro t ht
  simpa only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hev] using hall t

end C

theorem surj_of (h1 : DdNe l) (h2 : SecEx l) : Surj l := by
  intro s
  obtain ⟨t, ht⟩ := exists_det_ne s.1 (h1 s)
  let n : Sp l := ⟨lo t, lo_mem t⟩
  let m : Sp l := ⟨lo (-t), lo_mem (-t)⟩
  have e1 : (s * n).1.toBlocks₁₁.det ≠ 0 := by
    show (s.1 * lo t).toBlocks₁₁.det ≠ 0
    rw [toBlocks₁₁_mul_lo]
    exact ht
  have e2 : m.1.toBlocks₁₁.det ≠ 0 := by
    show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0
    simp [lo]
  obtain ⟨g1, -, hg1, -⟩ := h2 (s * n) e1
  obtain ⟨g2, -, hg2, -⟩ := h2 m e2
  refine ⟨g1 * g2, ?_⟩
  have hnm : n * m = 1 := Subtype.ext (lo_mul t)
  rw [map_mul, hg1, hg2, mul_assoc, hnm, mul_one]

end PositivityTheory.ThKR.Mp
end
end

