module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConditionsConjUnitaryKeepsStdLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfQ_of_hasInfExp (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : D.what₂.Tau → ℚ)
    (hc : ChrEq c χ) (h : ∀ τ, HasInfExp D c τ (e τ)) : χ.HasInfQ (tauE D) e := by
  classical
  choose n hn hx using h
  refine ⟨n, hn, fun k => ?_⟩
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θ, hθ⟩ : ∃ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ := ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro z
    have h1 : c (T.toHomUnits z) = ∏ τ, c (T.toHomUnits (Pi.mulSingle τ (z τ))) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle z]
      rw [map_prod, map_prod]
    have h2 := congrArg Circle.coeHom h1
    rw [map_prod] at h2
    refine h2.trans (Finset.prod_congr rfl fun τ _ => ?_)
    have h3 := (hx τ).2 θ hθ (T.toHomUnits (Pi.mulSingle τ (z τ))) (tf _) fun τ' hτ' =>
      (ti _ τ').trans (by rw [Pi.mulSingle_eq_of_ne hτ', Units.val_one])
    have h4 : θ τ (infPart D ((T.toHomUnits (Pi.mulSingle τ (z τ)) : (AE D)ˣ) : AE D)) = z τ :=
      (ti _ τ).trans (by rw [Pi.mulSingle_eq_same])
    rw [h4] at h3
    exact h3
  rw [← eq_inf D c χ hc k _ _ (hab _) (hb _).1 (hb _).2, hT _ (ha (Units.map (incA D).toMonoidHom k)).2, key]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h5 : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom (a (Units.map (incA D).toMonoidHom k)) : ℂˣ) : ℂ) =
      tauE D τ (k : D.host.E) :=
    (congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)
  rw [h5]

theorem hasInfExp_iff_hasInfQ : ∀ (D : D7) (c : GlobalTheory.Mem.Th.IdC D) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ),
    Formalism.IndefR.Links.ChrEq c χ → ((∀ τ, HasInfExp D c τ (a τ)) ↔ χ.HasInfQ (Formalism.L2.Host.embTau D) a) :=
  fun D c χ a hc => ⟨hasInfQ_of_hasInfExp D c χ a hc, hasInfExp_of_chrEq D c χ a hc⟩

end GlobalTheory.HeckeInfExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChrEqUnique

theorem eq_one_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} (h : ChrEq c 1) (x : (AE D)ˣ) : c x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D c h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) c 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

noncomputable def phase : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)])⟩
  map_one' := Circle.ext (by
    change ((1 : ℂˣ) : ℂ) / ((‖((1 : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = 1
    simp)
  map_mul' x y := Circle.ext (by
    change ((x * y : ℂˣ) : ℂ) / ((‖((x * y : ℂˣ) : ℂ)‖ : ℝ) : ℂ) =
      (x : ℂ) / ((‖(x : ℂ)‖ : ℝ) : ℂ) * ((y : ℂ) / ((‖(y : ℂ)‖ : ℝ) : ℂ))
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem continuous_phase : Continuous phase :=
  Continuous.subtype_mk (Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)) _

noncomputable def normPow (t : ℝ) : ℂˣ →* Circle where
  toFun z := Circle.exp (t * Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), mul_add,
      Circle.exp_add]

theorem continuous_normPow (t : ℝ) : Continuous (normPow t) :=
  Circle.exp.continuous.comp (continuous_const.mul
    (Units.continuous_val.norm.log fun z => norm_ne_zero_iff.2 z.ne_zero))

theorem eq_one_of_forall {z : ℂˣ} (h : ∀ φ : ℂˣ →* Circle, Continuous φ → φ z = 1) : z = 1 := by
  have hn : ‖(z : ℂ)‖ = 1 := by
    by_contra hne
    have hl : Real.log ‖(z : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 z.ne_zero) hne
    have h1 := h _ (continuous_normPow (Real.pi / Real.log ‖(z : ℂ)‖))
    change Circle.exp (_ * _) = 1 at h1
    rw [div_mul_cancel₀ _ hl] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp only [Circle.coe_exp, Complex.exp_pi_mul_I, Circle.coe_one] at h2
    norm_num at h2
  have h2 := congrArg (fun w : Circle => (w : ℂ)) (h _ continuous_phase)
  change (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 at h2
  rw [hn, Complex.ofReal_one, div_one] at h2
  exact Units.ext h2

theorem hchar_eq_one (D : D7) (ξ : HChar D.host.E) (h : ∀ P k, ξ.locK P k = 1) : ξ = 1 := by
  obtain ⟨Φ, hΦ, -, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Φ.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  refine Subtype.ext (MonoidHom.ext fun y => eq_one_of_forall fun φ hφ => ?_)
  have hc : ChrEq (φ.comp (ξ.1.comp u)) (1 : HChar D.host.E) := by
    refine ⟨⟨hφ.comp (ξ.2.1.comp hu), fun k => ?_⟩, fun P e he k x hx => ?_⟩
    · have : u (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (h1 k)
      change φ (ξ.1 (u _)) = 1
      rw [this, ξ.2.2, map_one]
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Φ (x : AE D) = _
        rw [hx, h2 P e he]
      have h3 : ξ.1 (localIdele D.host.E P (atFin P k)) = 1 := h P k
      change ((φ (ξ.1 (u x)) : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [this, h3, map_one]
      rfl
  have hy : u (Units.map Φ.symm.toRingHom.toMonoidHom y) = y := Units.ext (Φ.apply_symm_apply _)
  have := eq_one_of_chrEq hc (Units.map Φ.symm.toRingHom.toMonoidHom y)
  change φ (ξ.1 (u _)) = 1 at this
  rwa [hy] at this

theorem hchar_unique (D : D7) (c : IdC D) (χ χ' : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c χ') : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine hchar_eq_one D _ fun P k => ?_
  obtain ⟨Φ, -, -, -, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := PlaceIdem.exists_isPlIdem D j j1 j2 j3 P
  let x : (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom (localIdele D.host.E P (atFin P k))
  have hx : (x : AE D) = locE D e (k : D.host.E) := Φ.symm_apply_eq.2 (h2 P e he k).symm
  change χ.locK P k * (χ'.locK P k)⁻¹ = 1
  rw [mul_inv_eq_one]
  exact Units.ext ((h.2 P e he k x hx).symm.trans (h'.2 P e he k x hx))

theorem idc_unique (D : D7) (c c' : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) (h' : ChrEq c' χ) : c = c' := by
  have hc : ChrEq (c * c'⁻¹ : (AE D)ˣ →* Circle) (1 : HChar D.host.E) := by
    refine ⟨⟨h.1.1.mul h'.1.1.inv, fun x => ?_⟩, fun P e he k x hx => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h.1.2, h'.1.2, inv_one, one_mul]
    · change ((c x * (c' x)⁻¹ : Circle) : ℂ) = ((1 : ℂˣ) : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv, h.2 P e he k x hx, h'.2 P e he k x hx, mul_inv_cancel₀ (Units.ne_zero _)]
      rfl
  exact MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_chrEq hc x)

theorem isUnitary_of_chrEq (D : D7) (c : IdC D) (χ : HChar D.host.E) (h : ChrEq c χ) : χ.IsUnitary := by
  have hc := h.1
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := GlobalTheory.HeckeTensorRead.exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  let χ' : HChar D.host.E := ⟨Circle.toUnits.comp (MonoidHom.comp c u), ht.comp (hc.1.comp hu), fun k => by
    have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]⟩
  have h' : ChrEq c χ' := ⟨hc, fun P e he k x hx => by
    have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl⟩
  rw [hchar_unique D c χ χ' h h']
  exact fun x => Circle.norm_coe (c (u x))

theorem chrEq_unique : ∀ (D : D7), (∀ (c : IdC D) (χ χ' : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c χ' → χ = χ') ∧ (∀ (c c' : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → Formalism.IndefR.Links.ChrEq c' χ → c = c') ∧ ∀ (c : IdC D) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → χ.IsUnitary :=
  fun D => ⟨hchar_unique D, idc_unique D, isUnitary_of_chrEq D⟩

end GlobalTheory.ChrEqUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JetTransport

open MvPolynomial Finsupp

variable {ι : Type} [Fintype ι] {a b : ℕ}


open Classical in
noncomputable def wD (ι : Type) (a b : ℕ) : ((ι × Fin b × Fin b) ⊕ DVar ι a b) → (ι → ℕ) :=
  Sum.elim 0 fun x => Pi.single x.1 1


open Classical in
noncomputable def wF (ι : Type) (a : ℕ) : (ι × Fin a × Fin a) → (ι → ℕ) := fun v => Pi.single v.1 1

lemma weight_wF (e : (ι × Fin a × Fin a) →₀ ℕ) (τ : ι) :
    weight (wF ι a) e τ = ∑ α, ∑ s, e (τ, α, s) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wF, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma weight_wD (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (τ : ι) :
    weight (wD ι a b) u τ = ∑ β, ∑ α, u (Sum.inr (τ, β, α)) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wD, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

lemma jetMap_zero {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K) (P : Formalism.L2.DIV.Pol K ι a) :
    jetMap J (fun _ => 0) P = jetLin J (subD K ι a b P) := by
  simp [jetMap]

lemma jetLin_monomial {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K)
    (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial u c) = monomial (u.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (u.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have : (monomial u c : MvPolynomial _ K) = c • basisMonomials _ K u := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  unfold jetLin
  rw [LinearMap.map_smul, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

lemma jetLin_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (f ∘ J) (map f Q) = map f (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u c => simp [jetLin_monomial, map_monomial]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma subD_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : Formalism.L2.DIV.Pol K ι a) :
    subD K' ι a b (map f P) = map f (subD K ι a b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_X, map_mul, hp, map_mul, map_mul]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp [map_sum]

lemma subD_X_hom {K : Type} [Field K] (v : ι × Fin a × Fin a) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b (X v)) (wF ι a v) := by
  simp only [subD, aeval_X]
  split_ifs with h
  · apply IsWeightedHomogeneous.sum
    intro β _
    have := (isWeightedHomogeneous_X K (wD ι a b) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (wD ι a b) (Sum.inr (v.1, β, v.2.1)))
    simpa [wD, wF] using this
  · exact isWeightedHomogeneous_zero _ _ _

lemma subD_hom {K : Type} [Field K] (P : Formalism.L2.DIV.Pol K ι a) (n : ι → ℕ)
    (hP : IsWeightedHomogeneous (wF ι a) P n) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b P) n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  have hw : weight (wF ι a) e = n := hP (MvPolynomial.mem_support_iff.mp he)
  rw [subD, aeval_monomial, algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  rw [← hw, weight_apply]
  apply IsWeightedHomogeneous.prod
  intro v _
  simpa only [subD, aeval_X] using (subD_X_hom (b := b) (K := K) v).pow (e v)

lemma jetLin_congr {K : Type} [Field K] (J₁ J₂ : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) (hQ : IsWeightedHomogeneous (wD ι a b) Q n)
    (hJ : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J₁ m = J₂ m) :
    jetLin J₁ Q = jetLin J₂ Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [jetLin_monomial, jetLin_monomial, hJ]
  intro τ
  have hw := congrFun (hQ (MvPolynomial.mem_support_iff.mp hu)) τ
  rw [weight_wD] at hw
  simpa [Finsupp.comapDomain_apply] using hw

end GlobalTheory.JetTransport

theorem GlobalTheory.jetMapTransport : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  intro D p _ lam a b J J' n r A P hJ hP h
  classical
  let x : (DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m =>
    if hm : ∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ then (hJ m hm).choose else 0
  have hx1 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J m = (algebraMap Qbar ℂ ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.1.symm
  have hx2 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J' m = (lam ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.2.symm
  have hPw : ∀ {K : Type} [Field K] (f : Qbar →+* K),
      MvPolynomial.IsWeightedHomogeneous (GlobalTheory.JetTransport.wF D.what₂.Tau a) (MvPolynomial.map f P) n := by
    intro K _ f d hd
    funext τ
    rw [GlobalTheory.JetTransport.weight_wF]
    refine hP d (MvPolynomial.mem_support_iff.mpr fun h0 => hd ?_) τ
    rw [MvPolynomial.coeff_map, h0, map_zero]
  have key : ∀ {K : Type} [Field K] (f : Qbar →+* K) (JK : (DVar D.what₂.Tau a b →₀ ℕ) → K),
      (∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → JK m = (f ∘ x) m) →
      jetMap JK (fun _ => 0) (MvPolynomial.map f P) = MvPolynomial.map f (jetMap x (fun _ => 0) P) := by
    intro K _ f JK hJK
    rw [GlobalTheory.JetTransport.jetMap_zero, GlobalTheory.JetTransport.jetMap_zero, ← GlobalTheory.JetTransport.jetLin_map,
      ← GlobalTheory.JetTransport.subD_map]
    exact GlobalTheory.JetTransport.jetLin_congr _ _ n _ (GlobalTheory.JetTransport.subD_hom _ n (hPw f)) hJK
  have hA : A = MvPolynomial.C r * jetMap x (fun _ => 0) P := by
    apply MvPolynomial.map_injective (algebraMap Qbar ℂ) (algebraMap Qbar ℂ).injective
    rw [h, key (algebraMap Qbar ℂ) J hx1, map_mul, MvPolynomial.map_C]
    rfl
  rw [hA, map_mul, MvPolynomial.map_C, key lam J' hx2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentity
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.KerForm

open Classical

theorem frInv_leftInv {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ}
    (hi : i ≤ D.R.m) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ) : frInv O i (frPoly O i Q) = Q := by
  have hs : frInv O i ∘ₗ frPoly O i = LinearMap.id :=
    Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
      (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (Formalism.L2.Ker.frobenius_poly_injective D u C O i hi)))
  exact LinearMap.congr_fun hs Q

theorem sharp_evC (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (v : ValQ O u μ i) :
    (D.chTw u μ).sharp i (evC O u μ i v) = frPoly (O u μ) i
      (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  funext y
  rw [evC_sec]
  show (∏ τ, ((D.chTw u μ).de i y τ) ^ ((D.chTw u μ).sSharp i τ)) * ((∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)) = _
  show _ = GL3Theta.evFr D _ ((O u μ).frm i y)
  unfold srcPol GL3Theta.evFr
  rw [map_mul, map_mul, map_prod, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, map_pow, eval_detP, ← (O u μ).frm_de i hi.le y τ, ← zpow_add₀ ((D.chTw u μ).de_ne i y τ), ← zpow_natCast,
    Int.toNat_of_nonneg (sub_nonneg.2 (twLe D u μ i hi τ)), sub_eq_add_neg]

theorem complex_kform : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  intro D O u μ i hi hU c c' v v' h
  set Q := MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) with hQ
  set Q' := MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) with hQ'
  set ρ : ℂ := ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) with hρ
  have hunf : (D.chTw u μ).unf i c c' (frPoly (O u μ) i Q) =
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) := by
    rw [hU c c' Q]
    unfold unfC
    rw [LinearMap.comp_apply, LinearMap.comp_apply, frInv_leftInv (O u μ) hi.le]
  have hrho : (D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c' = ρ := by
    rw [((O u μ).c13 i hi).1 c, ((O u μ).c13 i hi).2 c']
  apply Formalism.L2.Ker.frobenius_poly_injective D u (D.chTw u μ) (O u μ) (i + 1) hi
  funext y'
  have h1 := congrFun h y'
  rw [ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, sharp_evC D O u μ i hi v, hunf, hrho] at h1
  rw [evC_sec] at h1
  change (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) * GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
    ρ * ((∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ *
      frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y') at h1
  have hne : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((D.chTw u μ).de_ne (i + 1) y' τ)
  have hinv : (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ (-((D.chTw u μ).sDiv i τ))) =
      (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun τ _ => zpow_neg _ _
  rw [hinv] at h1
  have h2 : GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') =
      ρ * frPoly (O u μ) (i + 1) (jetMap (ι := D.what₂.Tau) (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0) Q) y' := by
    have := inv_ne_zero hne
    apply mul_left_cancel₀ this
    rw [h1]; ring
  show GL3Theta.evFr D Q' ((O u μ).frm (i + 1) y') = GL3Theta.evFr D _ ((O u μ).frm (i + 1) y')
  rw [h2]
  simp [frPoly, GL3Theta.evFr]

end GlobalTheory.Mem.KerForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConditionsConjUnitaryKeepsStdLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (n : ℕ) (t s : GA B n)
    (x : ∀ w : (B.primes X).vGs, GL (Fin n) (𝓞 B.fields.E ⧸ w.1.asIdeal)) (h : GLG (E := B.fields.E) (n := n) (SG := (B.primes X).vGs)),
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E n) →
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∈ v.asIdeal → bc (prV (E := B.host.E) v) t = 1) →
    (∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((t : Matrix (Fin n) (Fin n) _) r j)) ((x w).1 r j)) →
    (LocalCondMoveDecoratedLattice u n (t⁻¹ * s * t) h ↔ LocalCondMoveDecoratedLattice u n s (fun w => x w * h w * (x w)⁻¹)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.conj_unitary_preserves_stdLat_of_ptOf <;> assumption)
end

