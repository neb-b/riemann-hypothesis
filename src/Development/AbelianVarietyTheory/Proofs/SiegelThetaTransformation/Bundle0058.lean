module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DefiniteGroupVacuumPhaseIndependentOfLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.VacPhase

theorem isMov_one {D : D7} {k : ℕ} (L : Lt D.host.E k) :
    IsMov (1 : Matrix (Fin k) (Fin k) (AfE D)) L L := by
  intro u
  simp only [Matrix.one_mulVec]
  exact ⟨fun h => ⟨u, h, rfl⟩, fun ⟨_, h, e⟩ => e ▸ h⟩

theorem conjI_ne_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) :
    conjI P ≠ ⊥ := by
  intro h
  apply hP
  rw [eq_bot_iff]
  intro b hb
  have h1 : GlobalTheory.SW.Nbr.co b ∈ conjI P := GlobalTheory.SW.Nbr.mem_conjI.2 (by rwa [GlobalTheory.SW.Nbr.co_co])
  rw [h, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot, ← GlobalTheory.SW.Nbr.co_co b, h1, map_zero]

theorem phase_indep : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ v₀ : Lt D.host.E T.rank → TF S.rank C.g, (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∃ ep : ℂ, ‖ep‖ = 1 ∧ ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → om (h, 1) (C.Th (C.xB B) (v₀ L)) = ep • (C.Th (C.xB B) (unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)))) := by
  intro D S T C om hom Lv hn M hidem hM hMm v₀ hv₀ B hB h Λ hh htriv hfg hmov
  obtain ⟨w, hw⟩ : ∃ w : Lt D.host.E T.rank → TF S.rank C.g,
      ∀ L, w L = unitv (projA C.X C.bas Lv.w (tens Λ (Lv.sh L)) (v₀ L)) := ⟨_, fun _ => rfl⟩
  have hx : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have hΛM : Λ ∈ Vset D.host.E S.rank M := (_root_.GlobalTheory.Ker.MovLev.mov_mem_lattices D S T C).1 M h Λ hM htriv hfg hmov
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := GlobalTheory.SW.stdL_mem_Vset M
  have h6833 := _root_.GlobalTheory.SW.level_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  have fmt_one : ∀ V : HSp D, fmt V 1 = 1 ∧ fmtC V 1 = 1 := fun V =>
    ⟨(((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).1,
      (((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 V).2.2.2.1 1 (one_mem _)).2.1⟩
  obtain ⟨μ, 𝓕, hcov⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).1
  obtain ⟨κ, hκ, hipTh⟩ := _root_.GlobalTheory.KerVacIp.ip_vacua D S T C μ 𝓕 hcov
  have hsd : ∀ L ∈ Lv.lats, SelfD C.X (Lv.sh L) := fun L hL => (h6833.2.2.2.1 L hL).1
  have hvac : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens Λ (Lv.sh L)) (w L) := fun L hL => by
    rw [hw L]
    exact GlobalTheory.SW.RecSum.isVac_unitv (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL) (hv₀ L hL)
  have hsbw : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (w L) := fun L hL => (hvac L hL).1
  have hsbv : ∀ L ∈ Lv.lats, GlobalTheory.SW.IsSB (v₀ L) := fun L hL => (hv₀ L hL).1
  have hS1 : ∀ Λ₀ : Lt D.host.E S.rank, IsMov (fmtC S 1) Λ₀ Λ₀ := fun Λ₀ => by
    rw [(fmt_one S).2]
    exact GlobalTheory.Ker.VacPhase.isMov_one Λ₀

  have phase : ∀ L ∈ Lv.lats, ∃ c : ℂ, ‖c‖ = 1 ∧
      om (h, 1) (C.Th (C.xB B) (v₀ L)) = c • C.Th (C.xB B) (w L) := fun L hL =>
    _root_.GlobalTheory.Ker.om_Th_vac D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hΛM _ _ (hsd L hL) (hsd L hL)
      h hh 1 (one_mem _) hmov (by rw [(fmt_one T).1]; exact GlobalTheory.Ker.VacPhase.isMov_one _)
      (v₀ L) (w L) (hv₀ L hL) (hvac L hL) B hB

  have pos : ∀ L ∈ Lv.lats, GlobalTheory.SW.ip (v₀ L) (w L) ≠ 0 ∧
      GlobalTheory.SW.ip (v₀ L) (w L) = ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) := by
    intro L hL
    obtain ⟨hne, heq⟩ := GlobalTheory.SW.RecSum.unitv_proj (D := Lv) C.idx C.sympl C.even hΛM (hsd L hL)
      (hv₀ L hL) (hvac L hL)
    rw [← hw L] at heq
    refine ⟨hne, ?_⟩
    have h1 : GlobalTheory.SW.ip (w L) (w L) = 1 := (hvac L hL).2.1
    have e : (GlobalTheory.SW.ip (v₀ L) (w L) / ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ)) * GlobalTheory.SW.ip (w L) (w L) =
        GlobalTheory.SW.ip (w L) (w L) := by
      rw [← GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), ← heq]
    rw [h1, mul_one] at e
    have hn0 : ((‖GlobalTheory.SW.ip (v₀ L) (w L)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
    exact (div_eq_one_iff_eq hn0).1 e
  have hXl : C.X.Λ ∈ Lv.lats := h6833.1
  obtain ⟨ep, hep1, hep⟩ := phase C.X.Λ hXl
  refine ⟨ep, hep1, ?_⟩
  intro g L hg hgtriv hLfg hgmov
  rw [← hw L]
  have hL : L ∈ Lv.lats := ((_root_.GlobalTheory.Ker.MovLev.mov_mem_lattices D S T C).2 Lv g L hLfg hgmov).2.1 hgtriv
  obtain ⟨c, hc1, hc⟩ := phase L hL
  rw [hc]

  have hXsd : SelfD C.X C.X.Λ := (show SelfD C.X C.X.Λ ∧ _ from hXl).1
  have hXfs : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨hXsd.1, (h6833.2.2.2.1 _ hXl).2.1⟩
  have hinv : fmt T g * fmt T g⁻¹ = 1 := by
    rw [← (((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.1 g g⁻¹).2.1, mul_inv_cancel, (fmt_one T).1]
  have hshmov : IsMov (fmt T g) (Lv.sh C.X.Λ) (Lv.sh L) :=
    ((((_root_.GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hXfs).2.2.2 (fmt T g) (fmt T g⁻¹) hinv).2 L hLfg hgmov).2.2.2.2
      Lv.𝔪 (conjI Lv.𝔪) Lv.ne_bot (GlobalTheory.Ker.VacPhase.conjI_ne_bot Lv.ne_bot)).2.1

  obtain ⟨a, ha1, ha⟩ := _root_.GlobalTheory.Ker.om_Th_vac D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hstd _ hstd _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (v₀ C.X.Λ) (v₀ L) (hv₀ _ hXl) (hv₀ L hL) B hB
  obtain ⟨b, hb1, hb⟩ := _root_.GlobalTheory.Ker.om_Th_vac D S T C om hom Lv.w Lv.w_int Lv.w_tr hidem M _ hΛM _ hΛM _ _
    (hsd _ hXl) (hsd L hL) 1 (one_mem _) g hg (hS1 _) hshmov (w C.X.Λ) (w L) (hvac _ hXl) (hvac L hL) B hB

  have hThX := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx _ (hsbv _ hXl)).1.1
  have hThwX := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hx _ (hsbw _ hXl)).1.1
  have hinvar := (((GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).2 μ 𝓕 hcov _ hThX).2.2.2 _ hThwX).2.2.2.2.2
    om hom (1, g)
  rw [ha, hb, ← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx _ (hsbv L hL)).2.1 a,
    ← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx _ (hsbw L hL)).2.1 b,
    hipTh B hB _ _ (GlobalTheory.SW.TensVac.sb_smul a (hsbv L hL)) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    hipTh B hB _ _ (hsbv _ hXl) (hsbw _ hXl),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbv L hL) (GlobalTheory.SW.TensVac.sb_smul b (hsbw L hL)),
    GlobalTheory.SW.TensVac.ip_smul_right _ (hsbv L hL) (hsbw L hL)] at hinvar
  have e1 : a * (conj b * GlobalTheory.SW.ip (v₀ L) (w L)) = GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ) :=
    mul_left_cancel₀ hκ hinvar
  obtain ⟨hpL0, hpL⟩ := pos L hL
  obtain ⟨-, hpX⟩ := pos _ hXl
  have hnorm : ‖GlobalTheory.SW.ip (v₀ C.X.Λ) (w C.X.Λ)‖ = ‖GlobalTheory.SW.ip (v₀ L) (w L)‖ := by
    rw [← e1, norm_mul, norm_mul, Complex.norm_conj, ha1, hb1, one_mul, one_mul]
  have e2 : (a * conj b) * GlobalTheory.SW.ip (v₀ L) (w L) = 1 * GlobalTheory.SW.ip (v₀ L) (w L) := by
    rw [mul_assoc, e1, one_mul, hpX, hnorm, ← hpL]
  have hab : a * conj b = 1 := mul_right_cancel₀ hpL0 e2
  have hbb : b * conj b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    norm_num
  have hab' : a = b := by
    calc a = a * (b * conj b) := by rw [hbb, mul_one]
      _ = (a * conj b) * b := by ring
      _ = b := by rw [hab, one_mul]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ha1
    exact zero_ne_one ha1

  have hsq : om (h, 1) (om (1, g) (C.Th (C.xB B) (v₀ C.X.Λ))) =
      om (1, g) (om (h, 1) (C.Th (C.xB B) (v₀ C.X.Λ))) := by
    have e : ((h, 1) : GA D S × GA D T) * (1, g) = (1, g) * (h, 1) := by simp
    have := congrArg (fun p => om p (C.Th (C.xB B) (v₀ C.X.Λ))) e
    simpa only [map_mul, Module.End.mul_apply] using this
  rw [ha, hep, map_smul, map_smul, hc, hb, smul_smul, smul_smul,
    ← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx _ (hsbw L hL)).2.1 (a * c),
    ← (_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx _ (hsbw L hL)).2.1 (ep * b)] at hsq
  have hfun := ((_root_.GlobalTheory.Ker.Ctx.th_laws D S T C _ hx _ (GlobalTheory.SW.TensVac.sb_smul (a * c) (hsbw L hL))).1 _
    (GlobalTheory.SW.TensVac.sb_smul (ep * b) (hsbw L hL))).2 hsq
  have e3 := congrArg (fun φ => GlobalTheory.SW.ip φ (w L)) hfun
  rw [GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL),
    GlobalTheory.SW.TensVac.ip_smul_left _ (hsbw L hL) (hsbw L hL), (hvac L hL).2.1, mul_one, mul_one,
    hab', mul_comm ep b] at e3
  rw [mul_left_cancel₀ (hab' ▸ ha0) e3]

end GlobalTheory.Ker.VacPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevEig

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} {X : Data E r} (L : SW.Level X)


end Alg

section Hat

variable {D : D7} {k : ℕ}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem tmul_mem_hatV {L : Lt D.host.E k} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : Fin k → D.host.E}
    (hx : x ∈ L) : (fun i => a ⊗ₜ[D.host.F] x i) ∈ hatV L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem toAf_mem {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) : toAf x ∈ hatV L :=
  tmul_mem_hatV one_mem_intAf hx

theorem toAf_sub (x y : Fin k → D.host.E) : toAf (x - y) = toAf x - toAf y := by
  funext i; exact TensorProduct.tmul_sub _ _ _

theorem hatV_map {G : Type} [AddCommGroup G] {L : Lt D.host.E k} (f : (Fin k → AfE D) →+ G) (H : AddSubgroup G)
    (h : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, f (fun i => a ⊗ₜ[D.host.F] x i) ∈ H) {u} (hu : u ∈ hatV L) : f u ∈ H := by
  refine (AddSubgroup.closure_le (H.comap f)).2 ?_ hu
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact h a ha x hx

theorem smul_mem_hatV {L L' : Lt D.host.E k} (c : 𝓞 D.host.E) (h : ∀ x ∈ L, c • x ∈ L') {u} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  refine hatV_map (DistribSMul.toAddMonoidHom _ ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E))) _
    (fun a ha x hx => ?_) hu
  convert tmul_mem_hatV ha (h x hx) using 1
  ext i
  simp [smul_eq_mul, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]

theorem nsmul_mem_hatV {L : Lt D.host.E k} {𝔪 : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ 𝔪) {u}
    (hu : u ∈ hatV L) : M • u ∈ hatV (𝔪 • L) := by
  have := smul_mem_hatV (L' := 𝔪 • L) M (fun x hx => Submodule.smul_mem_smul hM hx) hu
  have e : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : 𝓞 D.host.E) : D.host.E)) = (M : AfE D) :=
    map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)).toRingHom.comp
      (algebraMap (𝓞 D.host.E) D.host.E)) M
  rwa [e, Nat.cast_smul_eq_nsmul] at this

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {S T : HSp D}

theorem actO_sub (h : GA D S) (g : GA D T) (w w' : WO S T) :
    actO S T h g (w - w') = actO S T h g w - actO S T h g w' := by
  simp only [actO, Matrix.mul_sub, Matrix.sub_mul]

end Hat

section Mov

variable {D : D7} {S T : HSp D}

end Mov

section Main

variable {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X)

end Main

end GlobalTheory.Ker.LevEig
end

