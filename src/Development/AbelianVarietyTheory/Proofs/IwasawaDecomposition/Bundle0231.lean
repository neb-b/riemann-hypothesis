module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RatPt

variable {D : D7} {S T : HSp D}

theorem exists_fin_add_real (w : WO S T) :
    ∃ u v : WO S T, u.map (infPart D) = 0 ∧ v.map (finPart D) = 0 ∧ w = u + v := by
  let e : AE D := (pairA D.host.F 1 0) ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D e = 1 := rfl
  have h0 : finPart D e = 0 := by
    change (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  refine ⟨Matrix.of fun i j => (1 - e) * w i j, Matrix.of fun i j => e * w i j, ?_, ?_, ?_⟩
  · ext i j
    change infPart D ((1 - e) * w i j) = 0
    rw [RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, sub_self, zero_mul]
  · ext i j
    change finPart D (e * w i j) = 0
    rw [RingHom.map_mul, h0, zero_mul]
  · ext i j
    change w i j = (1 - e) * w i j + e * w i j
    rw [← add_mul, sub_add_cancel, one_mul]

theorem isTheta_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) : IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h : IsThetaFunO ψ S T (heisO ψ S T u (heisO ψ S T v f)) := by
    simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1
      (heisO ψ S T v f) (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf)
      Unit Finset.univ (fun _ => u) (fun _ => 1) (by intro i hi; exact hu)
  rw [GlobalTheory.WeilVacMove.heisO_heisO, (GlobalTheory.WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h
  exact h

theorem actO_one (h : GA D T) (w : WO S T) : actO S T 1 h w =
    HMul.hMul (Formalism.L2.Theta.mt T h) (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  rw [inv_one, GlobalTheory.Ker.OmRat.mt_one', Matrix.mul_one]

theorem compAt_mul (θ : InfFam D) (ρ : D.what₂.Tau) {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) :
    compAt θ ρ (x * y : Mx D a c) = compAt θ ρ x * compAt θ ρ y :=
  Matrix.map_mul (f := (θ ρ).comp (infPart D))

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {a b : ℕ}
    (m : Matrix (Fin a) (Fin b) D.host.E) : compAt θ ρ (m.map (incA D)) = m.map (tauE D ρ) := by
  ext i j
  exact (hθ ρ).1 (m i j)

theorem rational_points : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ δ ∈ GQ T, ∃ ga : GL (Fin r) D.host.E, Formalism.L2.Theta.mt T δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) ∧ IsUn X ga ∧ (∀ Z : Fam T, lact ga (frOf hr eT Z) = frOf hr eT (mvZ θ δ Z)) ∧ (∀ w : WO S T, (GlobalTheory.Ker.IsRealPt w → ∃ w' : WO S T, GlobalTheory.Ker.IsRealPt w' ∧ w = actO S T 1 δ w') ∧ ∀ τ k, rePt θ hr eT (actO S T 1 δ w) τ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ rePt θ hr eT w τ k) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ w, om (1, δ) f (actO S T 1 δ w) = f w := by
  intro D S T r g hr ψ θ X eT bas idx hS δ hδ
  subst hr
  obtain ⟨hψ, hθ, -, -, hM, -, he, -⟩ := hS
  obtain ⟨ga, hga, hδ'⟩ := id hδ
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have hc : ∀ τ : X.Ψ, compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) =
      (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 := fun τ => by
    rw [hm, compAt_rat hθ, ← he, Equiv.apply_symm_apply]
  refine ⟨ga, hm, ?_, fun Z => ?_, fun w => ⟨fun hw => ⟨actO S T 1 δ⁻¹ w, ?_, ?_⟩, fun τ k => ?_⟩, ?_⟩
  · intro x y
    have hG : X.Gm = (-T.gram)ᵀ := hM.1
    rw [hG, GlobalTheory.Ker.Grp.herm_eq, GlobalTheory.Ker.Grp.herm_eq]
    refine GlobalTheory.Ker.Grp.hform_mulVec _ _ _ ?_ _ _
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ga.1 * T.gram * ga.1 = T.gram := hga
    rw [Matrix.mul_neg, Matrix.neg_mul, h]
  · funext τ
    change (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 * Z (eT.symm τ) =
      compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) * Z (eT.symm τ)
    rw [hc]
  · unfold GlobalTheory.Ker.IsRealPt at hw ⊢
    rw [GlobalTheory.KerReal.map_actO, hw, Matrix.mul_zero, Matrix.zero_mul]
  · have := GlobalTheory.Ker.OmRat.actO_inv_cancel (1 : GA D S) δ w
    rw [inv_one] at this
    exact this.symm
  · funext a
    change compAt θ (eT.symm τ) (actO S T 1 δ w) a k = _
    rw [actO_one, compAt_mul, hc]
    rfl
  · intro χS χT om H f hf w
    have h1 := H.om_heis 1 δ w f hf
    have h2 := H.om_aut 1 (one_mem _) δ hδ _ (isTheta_heisO hψ hf w)
    rw [← GlobalTheory.Ker.OmRat.heisO_at_zero ψ _ (om (1, δ) f), ← h1]
    exact h2.trans (GlobalTheory.Ker.OmRat.heisO_at_zero _ _ _)

end GlobalTheory.OneMapRef.RatPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem subsingleton_coh_twist_pushforward_iff {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    {A N : LB X} (hA : A.IsLB) (hN : N.IsLB) (G : Y.Modules) [G.IsQuasicoherent] (j m p : ℕ) :
    Subsingleton (coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p) ↔
      Subsingleton (coh (twist ((Scheme.Modules.pushforward g).obj G)
        (tens (lbPow A j) (lbPow N m))) p) := by
  have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  have hA' := LB.isLB_pull hA g
  have hN' := LB.isLB_pull hN g
  have hT' : (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m)).IsLB :=
    isLB_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m)
  have hTp := LB.isLB_pull hT g
  have e : cls _ hT' = cls _ hTp := by
    apply (cls_eq_iff hT' hTp).2
    let a := chartPullPowPull A g j
    let b := chartPullPowPull N g m
    have c : ChartPull (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))
        (tens (lbPow A j) (lbPow N m)) g := by
      refine ⟨fun t => (a.idx t.1, b.idx t.2), fun t _ hz => ⟨a.le _ hz.1, b.le _ hz.2⟩, ?_⟩
      intro z i k hi hk
      exact (gm_tens _ _ (𝟙 Y) z i k hi hk).trans ((congrArg₂ (· * ·)
        (a.g z _ _ hi.1 hk.1) (b.g z _ _ hi.2 hk.2)).trans
          (gm_tens _ _ g z (a.idx i.1, b.idx i.2) (a.idx k.1, b.idx k.2)
            ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hk.1, b.le _ hk.2⟩).symm)
    exact LBIso.chartPull c (chartPullPull _ g) (PolBaseChange.lbIso_refl hT)
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq G hT' hTp e
  have := Twist.isQuasicoherent_twist (F := G) hTp
  have e₁ : coh (twist ((Scheme.Modules.pushforward g).obj G) (tens (lbPow A j) (lbPow N m))) p ≃ₗ[ℤ]
      coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p :=
    (cohOn.mapIso ℤ ⊤ p (Twist.projIso _ g G).symm).trans
      ((LinearEquiv.ofBijective (cohPushMap ℤ g (fun r => by simp) (twist G _) ⊤ p)
        (cohPushMap_bijective_of_isAffineHom ℤ g (fun r => by simp) (twist G _) ⊤ p)).trans (cohOn.mapIso ℤ ⊤ p i.symm))
  exact e₁.toEquiv.subsingleton_congr.symm

theorem twistConeVanishing_pull_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent],
    (TwistConeVanishing (A.pull g) (N.pull g) G ↔
      TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  intro X Y g _ A N hA hN G _
  unfold TwistConeVanishing
  simp only [subsingleton_coh_twist_pushforward_iff g hA hN G]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensor
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem twistConeVanishing_of_cut : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  intro Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩
  set φ := cutHom G hM s
  let ψ := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  let eK : kernel ψ ≅ kernel φ := (kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ
  have arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m →
      (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n) := by
    intro a n j m h₁ h₂
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h₁
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h₂
    simp only [Nat.add_sub_cancel_left]
    module
  set J := max j₁ (max jK jC) with hJ
  have hJ₁ : j₁ ≤ J := le_max_left _ _
  have hJK : jK ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : jC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p →
      Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hmj hJj p hp
      by_cases hm : m < 2 * r
      · exact h₁ j m (by omega) hm p hp
      · push_neg at hm
        have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
        have e₁ := Twist.shortExact_map hT hS₁
        have e₂ := Twist.shortExact_map hT hS₂
        obtain ⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅
            twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by
          refine nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT
            (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_
          rw [cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _),
            cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]
          exact arith _ _ j m (by omega) hm
        have hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1))
            (tens (lbPow A j) (lbPow N m))) ⊤ p) := by
          have := ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp
          exact (cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton
        have hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1)) := by
          have := hK j m (by omega) hmj (p + 1) (by omega)
          exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this
        have himg := cohOn.subsingleton₃ e₁ ⊤ p hmid hker
        exact cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)
  exact ⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩

end GlobalTheory
end
end

