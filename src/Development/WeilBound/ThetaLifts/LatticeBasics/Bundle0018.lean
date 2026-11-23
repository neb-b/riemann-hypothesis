module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0004
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0012
public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
public import Development.WeilBound.ThetaLifts.LatticeBasics.FinOrbit
public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0032

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.WeilM Hgt

theorem hgtEx_of (hK : Stab2Cpt) : HgtEx := fun F E _ _ _ _ _ σ B n Y r s hB hY =>
  hgtEx_core hB hY (hK F E σ B n Y r s hB hY _ (isStab2_stab2 B))

theorem Hgt.graph_alg {S ι : Type} [CommRing S] [Fintype ι] [DecidableEq ι] (c : S →+* S) {g g' t t' : Matrix ι ι S} (hg : g * g' = 1)
    (ht : t' = g' * t) (hd : g'.det * c g'.det = 1) :
    (t.det * c t.det) • g = c t'.det • (t * t'.adjugate) ∧ (t.det * c t.det) • g' = c t.det • (t' * t.adjugate) := by
  constructor
  · have e : t = g * t' := by rw [ht, ← Matrix.mul_assoc, hg, Matrix.one_mul]
    conv_rhs => rw [e, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [ht, Matrix.det_mul, map_mul]
    congr 1
    linear_combination (-(t.det * c t.det)) * hd
  · rw [ht, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

theorem hgtInt_of (hC : Stab2Cpt) : HgtInt := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K a e hK ha he μ hμ
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have cK := hC F E σ B n Y r s hB hY K hK
  obtain ⟨⟨K', a', hK', ha', ca, a0⟩, e', ce, he'⟩ := hgtEx_of hC F E σ B n Y r s hB hY
  obtain rfl : K = K' := Subgroup.ext fun k => (hK k).trans (hK' k).symm
  obtain rfl : a = a' := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha'.val p t hp k hk]
  obtain rfl : e = e' := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he x.1 x.2).trans (he' x.1 x.2).symm))
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  let T : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₁
  let T' : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₂
  have cm : Continuous fun k : G2 σ Y => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_mul continuous_const
  have cT : Continuous T := cm.matrix_submatrix _ _
  have cT' : Continuous T' := cm.matrix_submatrix _ _
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
  let c := (Module.Free.chooseBasis (AF F) (Matrix (Fin n) (Fin n) (AE F E))).equivFun
  obtain ⟨R, C, b, h1, h2, h3, h4⟩ := count_ad (E := E) hB.cm.1 c (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap) (UG (cA σ) (incM F Y.J))
    (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const)
    ((cK.image ((cc.comp cT'.matrix_det).smul (cT.matrix_mul cT'.matrix_adjugate))).union
      (cK.image ((cc.comp cT.matrix_det).smul (cT'.matrix_mul cT.matrix_adjugate))))
    (cK.image (continuous_norm_tens.comp cT.matrix_det)) μ
  have key : ∀ g : UA σ Y.J, ∃ k ∈ K, ∃ t : GL (Fin n) (AE F E), a (e (1, g)) = absE F E (Matrix.GeneralLinearGroup.det t) ∧
      T k = t.1 ∧ T' k = mat g⁻¹ * t.1 := fun g => by
    obtain ⟨p, t, hp, k, hk, h⟩ := ha.iwa (e (1, g))
    have e1 : k⁻¹ = e (1⁻¹, g⁻¹) * p := by rw [← Prod.inv_mk, map_inv, h]; group
    have hp' : (mat2 p * diagCols (E := AE F E) (Fin n)) = (diagCols (E := AE F E) (Fin n) * t.1) := hp
    have e2 : (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) = Matrix.fromRows t.1 (mat g⁻¹ * t.1) := by
      rw [e1, show mat2 (e (1⁻¹, g⁻¹) * p) = mat2 (e (1⁻¹, g⁻¹)) * mat2 p from rfl, Matrix.mul_assoc, hp', he, inv_one,
        show mat (1 : UA σ Y.J) = 1 from rfl, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
      simp
    exact ⟨k, hk, t, by rw [h, ha.val p t hp k hk], congrArg Matrix.toRows₁ e2, congrArg Matrix.toRows₂ e2⟩
  refine integrable_of_count μ (ca.comp (ce.comp (Continuous.prodMk_right 1))).measurable (fun g => a0 _) (R := R) h1 (fun g => ?_)
    h2 b fun j => (measure_mono fun g hg => ?_).trans (h4 j)
  · obtain ⟨k, hk, t, e1, e2, -⟩ := key g
    exact e1.trans_le (h3 _ ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩)
  · obtain ⟨k, hk, t, e1, e2, e3⟩ := key g
    have hd : (mat g⁻¹).det * (cA σ).toRingHom (mat g⁻¹).det = 1 := by
      have h := congrArg Matrix.det (show (mat g⁻¹)ᵀ * incM F Y.J * (mat g⁻¹).map (cA σ) = incM F Y.J from (g⁻¹).2)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show ((mat g⁻¹).map (cA σ)).det = (cA σ).toRingHom (mat g⁻¹).det from ((cA σ).toRingHom.map_det _).symm] at h
      refine (isUnit_det_JR (R := AF F) (det_ne hY)).mul_left_cancel ?_
      change (incM F Y.J).det * _ = (incM F Y.J).det * _
      linear_combination h
    obtain ⟨q1, q2⟩ := Hgt.graph_alg (cA σ).toRingHom (g := mat g) g.1.mul_inv e3 hd
    have q : ∀ X : Matrix (Fin n) (Fin n) (AE F E), Algebra.norm (AF F) t.1.det • X = (t.1.det * (cA σ).toRingHom t.1.det) • X :=
      fun X => by rw [← algebraMap_smul (AE F E), algebraMap_norm_eq hB.cm, ← cA_eq]; rfl
    refine ⟨Matrix.GeneralLinearGroup.det t, ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩, e1 ▸ hg,
      .inl ⟨k, hk, Eq.symm ((q _).trans (q1.trans ?_))⟩, .inr ⟨k, hk, Eq.symm ((q _).trans (q2.trans ?_))⟩⟩ <;> rw [← e2] <;> rfl

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem polFin {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χX χW} {om : Rep σ Y W} {r s r' s'}
    (h : IsPair B M χX χW om r s r' s') : ∀ f ∈ M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)),
      FiniteDimensional ℂ U ∧ ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U := by
  intro f hf
  have hψ := h.base.std
  have hs := h.weil.isUSplitting.toIsSplitting
  let S : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
        ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U}
      zero_mem' := ⟨⊥, inferInstance, fun k _ A _ => by rw [map_zero]; exact zero_mem _⟩
      add_mem' := by
        rintro f g ⟨N, _, h1⟩ ⟨N', _, h2⟩
        exact ⟨N ⊔ N', inferInstance, fun k hk A hA => by
          rw [map_add (f := _)]; exact Submodule.add_mem_sup (h1 k hk A hA) (h2 k hk A hA)⟩
      smul_mem' := fun c f ⟨N, h0, h1⟩ => ⟨N, h0, fun k hk A hA => by rw [map_smul]; exact N.smul_mem c (h1 k hk A hA)⟩ }
  have hfS : f ∈ S := by
    refine (sInf_le (a := S) ⟨fun f₀ h₀ => ?_, fun u hu g ⟨N, h0, h1⟩ g₁ hg => ?_⟩ : M.Pol B.ψ B.emb ≤ S) hf
    · haveI := Dense.vacSp_fin h.base.cm M B.emb
      refine ⟨⨆ ε, Dense.vacSp M B.emb ε, inferInstance, fun k hk A hA => ?_⟩
      have hgauss : M.IsGauss B.ψ B.emb (A f₀) := by
        obtain ⟨ε, hε⟩ := h₀
        refine ⟨ε, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
        set N := (mat k⁻¹).transpose with hN
        have hNk : N * (mat k).transpose = 1 := by
          rw [hN, ← Matrix.transpose_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.transpose_one]
        have e1 : u * N * (mat k).transpose = u := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have e2 : u' * N * (mat k).transpose = u' := by rw [Matrix.mul_assoc, hNk, Matrix.mul_one]
        have hf1 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hf
        have hf2 := PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu' hf'
        have i1 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀
        have i2 := PositivityTheory.ThKOwn.KPol.inter hψ hs hA (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀
        rw [e1, ← hf1] at i1
        rw [e2, ← hf2] at i2
        have hcomm : ∀ w, Commute ((mat k⁻¹).map (piInf (B.emb w))) (W.θ w) := fun w => by
          have hc : Commute ((mat k).map (piInf (B.emb w))) (W.θ w) := hk.2 w
          have h1 : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
          have h2 : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := by
            rw [← Matrix.map_mul, PositivityTheory.ThKOwn.KPol.mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
          show _ * _ = _ * _
          calc (mat k⁻¹).map (piInf (B.emb w)) * W.θ w
              = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w * ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by
                rw [h2, Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) * (mat k⁻¹).map (piInf (B.emb w)) := by
                simp only [Matrix.mul_assoc]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * ((mat k).map (piInf (B.emb w)) * W.θ w) * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [hc.eq]
            _ = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
                rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hrel' : ∀ w, (u' * N).map (piInf (B.emb w)) =
            (((ε w : ℤ) : ℂ) * Complex.I) • (Y.θ w * (u * N).map (piInf (B.emb w)) * (W.θ w).transpose) := fun w => by
          have hN' : N.map (piInf (B.emb w)) = ((mat k⁻¹).map (piInf (B.emb w))).transpose := by
            rw [hN, Matrix.transpose_map]
          have hc : (W.θ w).transpose * N.map (piInf (B.emb w)) = N.map (piInf (B.emb w)) * (W.θ w).transpose := by
            rw [hN', ← Matrix.transpose_mul, ← Matrix.transpose_mul, (hcomm w).eq]
          rw [Matrix.map_mul, Matrix.map_mul, hrel w, Matrix.smul_mul]
          simp only [Matrix.mul_assoc, hc]
        have hg := hε (u * N) (u' * N) (PositivityTheory.ThKOwn.KPol.at_mul hu N) (PositivityTheory.ThKOwn.KPol.at_mul hu' N) hrel' _ _
          (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu N) f₀) (PositivityTheory.ThKOwn.KPol.actsD_dop M hψ (PositivityTheory.ThKOwn.KPol.at_mul hu' N) f₀)
        rw [← i1, ← i2, hg, map_smul]
      obtain ⟨ε, hε⟩ := hgauss
      exact Submodule.mem_iSup_of_mem ε fun u u' hu hu' e => hε u u' hu hu' e _ _ (Dense.actsD_dop M hψ hu _)
        (Dense.actsD_dop M hψ hu' _)
    · obtain ⟨N', h3, h4⟩ := Dense.exists_dop_fin N
      refine ⟨N', h3, fun k hk A hA => ?_⟩
      rw [PositivityTheory.ThKOwn.KPol.actsD_unique M hψ hu hg, PositivityTheory.ThKOwn.KPol.inter hψ hs hA hu]
      exact h4 _ _ _ (h1 k hk A hA)
  change ∃ U : Submodule ℂ (SInf F (Fin n × Fin d)), FiniteDimensional ℂ U ∧
    ∀ k ∈ KInf σ W B.emb, ∀ A, PositivityTheory.ThKOwn.KPol.Impl om k A → A f ∈ U at hfS
  obtain ⟨U, h0, h1⟩ := hfS
  refine ⟨U, h0, fun k hk f₁ h₁ => ?_⟩
  obtain ⟨A, hA⟩ := PositivityTheory.ThKOwn.KPol.exists_impl fun f => PositivityTheory.ThKOwn.KPol.exists_arch_operator hψ hs hk.1 f
  rw [PositivityTheory.ThKOwn.KPol.acts_unique hA h₁]
  exact h1 k hk A hA

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.RankPolData
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Cardinal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def CptOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∃ K : Subgroup (UA σ Y.J), IsOpen (K : Set (UA σ Y.J)) ∧ IsCompact (K : Set (UA σ Y.J))

def PolRank : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀

namespace Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W}

theorem rank_polData (hM : M.IsGood B.ψ) (h : Module.rank ℂ (M.Pol B.ψ B.emb) ≤ ℵ₀) : Module.rank ℂ (PolData B M) ≤ ℵ₀ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  let p : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → Af F) → ℂ) →ₗ[ℂ] Fn F n d :=
    LinearMap.mk₂ ℂ (fun f g => pureA F f g) (fun _ _ _ => funext fun _ => add_mul _ _ _)
      (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
      (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)
  have le : PolData B M ≤ Submodule.map₂ p (M.Pol B.ψ B.emb) (SB _) := Submodule.span_le.2 (by
    rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hM φ h1 h2
    exact e f ▸ Submodule.apply_mem_map₂ p hf hg)
  refine (Submodule.rank_mono le).trans ?_
  rw [TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  refine (LinearMap.rank_le_domain _).trans ?_
  rw [rank_tensorProduct']
  exact (mul_le_mul' h (GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank.rank_SB_le _)).trans Cardinal.aleph0_mul_aleph0.le

def Il {χ χ' : Chr F E} (hw : M.IsWeil B.ψ χ χ' om) (hc : ∀ Φ ∈ schA F _, M.Conv om Φ) :
    schA F (Fin n × Fin d) →ₗ[ℂ] (UA σ W.J → ℂ) where
  toFun Φ := M.I om Φ
  map_add' Φ Ψ := funext (PositivityTheory.ThKG.I_add hw hc Φ.2 Ψ.2)
  map_smul' c Φ := funext (PositivityTheory.ThKG.I_smul M om c Φ)

theorem I_rt (Φ : Fn F n d) (g h : UA σ W.J) : M.I om (om (1, g) Φ) h = M.I om Φ (h * g) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem exists_form {J : Matrix (Fin n) (Fin n) E} (c : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u u' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (hc : ∀ x, Continuous (u x)) (hc' : ∀ x, Continuous (u' x)) (hi : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u x (γ * g) = u x g)
    (hi' : ∀ x, ∀ γ ∈ ratU σ J, ∀ g, u' x (γ * g) = u' x g) (ρ : UA σ J →* Module.End ℂ P)
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (he' : ∀ g x h, u' (ρ g x) h = u' x (h * g)) :
    ∃ b : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ, (∀ x y, b x y = pet μ D (u y) (u' x)) ∧ ∀ g x y, b (ρ g x) (ρ g y) = b x y := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 (c.fin _ _ hμ hD).ne
  have ii : ∀ x y, Integrable (fun g => u y g * star (u' x g)) (μ.restrict D) := fun x y => by
    have h := (hc y).mul (hc' x).star
    obtain ⟨C, hC⟩ := c.bdd h fun γ hγ g => by simp only [Pi.mul_apply, Pi.star_apply, hi y γ hγ, hi' x γ hγ]
    exact Integrable.of_bound h.aestronglyMeasurable C (Eventually.of_forall hC)
  haveI := c.cnt
  haveI := c.right μ hμ
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => pet μ D (u y) (u' x))
    (fun x x' y => ?_) (fun a x y => ?_) (fun x y y' => ?_) (fun a x y => ?_), fun _ _ => rfl, fun g x y => ?_⟩
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x' y)]; simp [mul_add]
  · simp [pet, ← integral_const_mul, mul_left_comm]
  · rw [pet, pet, pet, ← integral_add (ii x y) (ii x y')]; simp [add_mul]
  · simp [pet, ← integral_const_mul, mul_assoc]
  · simp only [LinearMap.mk₂'ₛₗ_apply, pet, he, he']
    exact PositivityTheory.ThKF.L2.integral_right hD (fun h => u y h * star (u' x h)) (fun γ hγ h => by rw [hi y γ hγ, hi' x γ hγ]) g

theorem line_cpt {J : Matrix (Fin n) (Fin n) E} (cW : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {P : Type} [AddCommGroup P] [Module ℂ P] {u v v' : P →ₗ[ℂ] (UA σ J → ℂ)}
    (ρ : UA σ J →* Module.End ℂ P) (H : ∀ w ∈ ({u, v, v'} : Set _), (∀ x, Continuous (w x)) ∧
      (∀ x, ∀ γ ∈ ratU σ J, ∀ g, w x (γ * g) = w x g) ∧ (∀ g x h, w (ρ g x) h = w x (h * g)) ∧ ∀ x, u x = 0 → w x = 0)
    (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀) (K : Subgroup (UA σ J)) (k1 : IsOpen (K : Set (UA σ J)))
    (k2 : IsCompact (K : Set (UA σ J)))
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, pet μ D (v x) (v' y) = lam * pet μ D (u x) (u y) := by
  obtain ⟨a1, a2, a3, a4⟩ := H u (by simp)
  obtain ⟨b1, b2, b3, b4⟩ := H v (by simp)
  obtain ⟨c1, c2, c3, c4⟩ := H v' (by simp)
  obtain ⟨b, eb, ib⟩ := exists_form cW hμ hD b1 c1 b2 c2 ρ b3 c3
  obtain ⟨c, ec, ic⟩ := exists_form cW hμ hD a1 a1 a2 a2 ρ a3 a3
  obtain ⟨Ω, hΩ, cov⟩ := cW.cov
  have := cW.lc
  have := cW.t2
  obtain ⟨lam, hl⟩ := line ρ u a1 a3 hr K k1 k2 hΩ (fun g => (cov g).elim fun γ hγ => ⟨_, hγ.2, fun x => (a2 x γ hγ.1 g).symm⟩)
    b c ib ic (fun x y => by rw [ec, ec, pet, pet, ← integral_conj]; simp [mul_comm])
    (fun x => by
      rw [ec, pet, show (fun h => u x h * star (u x h)) = fun h => ((‖u x h‖ ^ 2 : ℝ) : ℂ) from
        funext fun h => by simp [Complex.mul_conj'], integral_complex_ofReal]
      exact integral_nonneg fun _ => by positivity)
    (fun x hx => cW.eq_zero hμ hD (a1 x) (a2 x) (ec x x ▸ hx))
    (fun x hx => LinearMap.ext fun y => by rw [eb, c4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, eb, b4 x hx]; simp [pet])
    (fun x hx => LinearMap.ext fun y => by rw [LinearMap.flip_apply, ec, a4 x hx]; simp [pet]) irr
  exact ⟨lam, fun x y => by rw [← eb, ← ec, hl]⟩

end Herm

open Herm in
theorem hermLine_of (hC : CptAll) (hK : CptOpen) (hR : PolRank) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h hp hq μ D hμ hD s t s' t'
  have T := h.triple
  have cW := hC F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨K, k1, k2⟩ := hK F E σ B _ G.W _ _ T.base (Or.inr T.geo.hW) (by omega)
  obtain ⟨-, m2, m3⟩ := hM F E σ B a a' G X om om' R Rf h
  obtain ⟨st1, st2⟩ := hS F E σ B a a' G X om om' R Rf h hp hq
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf h
  have z0 : (0 : Fn F a (a + a') × Fn F a' (a + a')) ∈ pairs B G X R Rf :=
    ⟨zero_mem _, X.T, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, by simp⟩
  let P : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) :=
    { carrier := pairs B G X R Rf
      zero_mem' := z0
      add_mem' := fun hx hy => by simpa using st1 _ hx _ hy 1
      smul_mem' := fun c x hx => by simpa using st1 _ z0 _ hx c }
  have s1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM (m3 _ _ y.2.1 y.2.2).1
  have s2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => PositivityTheory.ThKG.polData_le T.geo.hM' (m3 _ _ y.2.1 y.2.2).2.1
  let I₁ := Il T.weil fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T) (Or.inr (by omega))).1 Φ hΦ).1
  let I₂ := Il T.weil' fun Φ hΦ => ((hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T) (Or.inr (by omega))).1 Φ hΦ).1
  let j₂ := (LinearMap.snd ℂ _ _ ∘ₗ P.subtype).codRestrict _ s2
  let io : ℂ → ℂ → P →ₗ[ℂ] (UA σ G.W.J → ℂ) := fun s t =>
    s • I₁ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ P.subtype).codRestrict _ s1 + t • I₂ ∘ₗ j₂
  have eio : ∀ s t y, io s t y = comb G om om' s t y.1 := fun _ _ _ => rfl
  have e01 : ∀ y, io 0 1 y = G.M'.I om' y.1.2 := fun y => by simp [eio, comb]
  let ρ : UA σ G.W.J →* Module.End ℂ P :=
    { toFun := fun g => ((om (1, g)).prodMap (om' (1, g))).restrict fun y hy => st2 y hy g
      map_one' := LinearMap.ext fun y => Subtype.ext (show (om 1 y.1.1, om' 1 y.1.2) = y.1 by simp)
      map_mul' := fun g g' => LinearMap.ext fun y => Subtype.ext
        (show (om (1, g * g') y.1.1, om' (1, g * g') y.1.2) = (om (1, g) (om (1, g') y.1.1), om' (1, g) (om' (1, g') y.1.2)) by
          simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]) }
  have he : ∀ s t g y x, io s t (ρ g y) x = io s t y (x * g) := fun s t g y x =>
    show s * G.M.I om (om (1, g) y.1.1) x + t * G.M'.I om' (om' (1, g) y.1.2) x = _ by rw [I_rt, I_rt]; rfl
  have cc : ∀ s t y, Continuous (io s t y) := fun s t y =>
    (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 (Or.inr (by omega)) _ (s1 y)).const_smul s).add
      (((hI F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 (Or.inr (by omega)) _ (s2 y)).const_smul t)
  have ci : ∀ s t y, ∀ γ ∈ ratU σ G.W.J, ∀ g, io s t y (γ * g) = io s t y g := fun s t y γ hγ g => by
    have b1 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV T)).1 _ (s1 y)).2.1 1 (one_mem _) γ hγ
    have b2 := ((hB F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' T)).1 _ (s2 y)).2.1 1 (one_mem _) γ hγ
    simp only [one_mul] at b1 b2
    simp only [eio, comb, Pi.add_apply, Pi.smul_apply, Model.I, b1, b2]
  have nul : ∀ s t (y : P), PolMatch B G X R Rf y.1.1 0 → io s t y = 0 := fun s t y hy => by
    have := st1 _ y.2 (y.1.1, 0) ⟨zero_mem _, hy⟩ (-1)
    rw [show y.1 + (-1 : ℂ) • (y.1.1, 0) = (0, y.1.2) by ext <;> simp] at this
    rw [eio, comb, f1 _ hy, f2 _ y.2.1 this.2]; simp
  have irr : ∀ N : Submodule ℂ P, LinearMap.ker (io 0 1) ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) →
      (∀ y ∈ N, PolMatch B G X R Rf y.1.1 0) ∨ N = ⊤ := fun N h1 h2 =>
    (hJ F E σ B a a' G X om om' R Rf h hp hq (N.map P.subtype) (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      (fun y hy h0 => ⟨⟨y, hy⟩, h1 (nul 0 1 ⟨y, hy⟩ h0), rfl⟩) (by rintro _ ⟨y, hy, rfl⟩ g; exact ⟨_, h2 g y hy, rfl⟩)).imp
      (fun h y hy => h _ ⟨y, hy, rfl⟩) fun h => eq_top_iff.2 fun y _ => by
        obtain ⟨z, hz, e⟩ := h y.2
        exact (Subtype.ext e : z = y) ▸ hz
  have ker : ∀ s t y, io 0 1 y = 0 → io s t y = 0 := fun s t y hy => by
    refine (irr _ le_rfl fun g x hx => funext fun z => ?_).elim (fun h => nul s t y (h y hy)) fun h0 => ?_
    · rw [he, show io 0 1 x = 0 from hx]; rfl
    · obtain ⟨Φ', r1, r2⟩ := (hN F E σ B a a' G X om om' T).2 hq
      obtain ⟨Φ, hΦ⟩ := m2 Φ' r1.1
      exact absurd ((e01 ⟨(Φ, Φ'), r1.2, hΦ⟩).symm.trans (h0.ge trivial)) r2
  have le : LinearMap.range (io 0 1) ≤ ((PolData B G.M').comap (schA F _).subtype).map I₂ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨j₂ y, (m3 _ _ y.2.1 y.2.2).2.1, (e01 y).symm⟩
  obtain ⟨lam, hl⟩ := line_cpt cW hμ hD (u := io 0 1) (v := io s t) (v' := io s' t') ρ
    (by rintro _ (rfl | rfl | rfl) <;> exact ⟨cc _ _, ci _ _, he _ _, ker _ _⟩)
    ((Submodule.rank_mono le).trans ((rank_map_le _ _).trans
      ((Submodule.comapSubtypeEquivOfLe (PositivityTheory.ThKG.polData_le T.geo.hM')).rank_eq.trans_le
        (rank_polData T.geo.hM' (hR F E σ B _ _ _ _ _ _ _ _ _ T.base T.geo.hV' T.geo.hW))))) K k1 k2
    fun N h1 h2 => (irr N h1 h2).imp_left fun h y hy => nul 0 1 y (h y hy)
  exact ⟨lam, fun y hy y' hy' => hl ⟨y, hy⟩ ⟨y', hy'⟩⟩

end GlobalTheory.ThK.Dbl

end
end

