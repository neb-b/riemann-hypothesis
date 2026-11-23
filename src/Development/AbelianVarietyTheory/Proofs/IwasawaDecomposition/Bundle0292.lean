module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspBoundSiegel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_mul (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    posIdele (K := E) (ρ * σ) (mul_pos hρ hσ) = posIdele ρ hρ * posIdele σ hσ := by
  unfold posIdele
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← map_mul]
  congr 1
  exact Subtype.ext (mul_pow ρ σ _)

theorem posIdele_exp (u : ℝ) :
    posIdele (K := E) (Real.exp u) (Real.exp_pos u) = infId E (expU fun _ : InfinitePlace E => (u : ℂ)) := by
  refine Units.ext (ad_ext ?_ ?_)
  · have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
    funext w
    have hc := IsTotallyComplex.isComplex w
    have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (posRealElem w _) = _
    unfold posRealElem
    rw [dite_eq_right hw, RingEquiv.apply_symm_apply]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]
  · change ((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_congr {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

theorem diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    diagUnits a (fun _ : Fin a => posIdele (K := E) x hx) = splitCentre E a (Real.log x) := by
  rw [splitCentre_eq_scalar, ← posIdele_exp, posIdele_congr hx (Real.exp_pos _) (Real.exp_log hx).symm]
  refine Units.ext ?_
  rw [coe_diagUnits]
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_posIdele_pos :
    Continuous fun r : {r : ℝ // 0 < r} => (posIdele (K := E) r.1 r.2 : IdeleGroup E) := by
  unfold posIdele
  exact continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp
    (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem ideleModule_det_diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
      (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx))) : ℝ) = x ^ (a * Module.finrank ℚ E) := by
  have hdet : Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx)) =
      posIdele x hx ^ a := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rw [hdet, map_pow, Positive.val_pow, ideleModule_posIdele, ← pow_mul, mul_comm]

theorem cuspFormsBounded_of_rapidDecay (h : GlobalTheory.Published.CuspRapidDecaySiegelGL) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hA
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨‖φ.1 1‖, fun g => ?_⟩
    have : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : a * d ≠ 0 := (Nat.mul_pos ha hd0).ne'
  set m : AdelicGLn.AdelicGL E a → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (a * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a :=
    fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  have hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits a).comp
    (continuous_pi fun _ => continuous_posIdele_pos.comp hsc)).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  obtain ⟨C, hC⟩ := h E a φ hφ (f '' ω) hω'c hω'B hω'1 t ht 0
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← posIdele_mul]
    exact posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E a γ * g = _
    rw [e, hD, diagUnits_posIdele a hρpos, splitCentre_add]
    simp only [hf, diagUnits_posIdele a (hspos b)]
    symm
    calc splitCentre E a (Real.log (s b)) * splitCentre E a (Real.log ρ) *
          (b * (splitCentre E a (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E a (Real.log (s b)) * (splitCentre E a (Real.log ρ) *
            (b * (splitCentre E a (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E a (Real.log (s b)) * ((b * (splitCentre E a (Real.log (s b)))⁻¹) *
            splitCentre E a (Real.log ρ)) * D' * k := by rw [splitCentre_comm (Real.log ρ)]
      _ = (splitCentre E a (Real.log (s b)) * b) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E a (Real.log (s b))) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by rw [splitCentre_comm (Real.log (s b)) b]
      _ = b * (splitCentre E a (Real.log ρ) * D') * k := by group
  calc ‖φ.1 g‖ = ‖φ.1 (ratGL E a γ * g)‖ := by rw [hφ.1.left]
    _ = ‖φ.1 (f b * D' * k)‖ := by rw [key, hA]
    _ ≤ C * ∏ i, r' i ^ (0 : Fin a → ℝ) i := hC (f b) ⟨b, hb, rfl⟩ r' hr'pos (fun i j hij => by
          simp only [hr']
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by
          simp only [hr']
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
            div_self hprod.ne']) k hk
    _ = C := by simp

end GlobalTheory.CuspBoundSiegel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLiftFlagGroupInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.ProjectorAdjoint

open Formalism.IndefR.Lev

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G] {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem isLiftFlagGroup_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) : IsLevelLift V β L g⁻¹ κ⁻¹ := by
  refine ⟨(GfC V).inv_mem h.1, ?_, ?_⟩
  · rw [map_inv]; exact Subgroup.inv_mem _ h.2.1
  · rw [map_inv, rTup_inv h.2.1, h.2.2]

theorem levChi_inv {g : G0 L.Pg L.r} {κ : GA D V} (h : IsLevelLift V β L g κ) :
    (levChi V β (flagL L) κ⁻¹)⁻¹ = star (levChi V β (flagL L) κ)⁻¹ := by
  have h1 : κ ∈ levG V β (flagL L) := ⟨h.1, h.2.1, Subgroup.mem_top _⟩
  have hn := GlobalTheory.norm_levChi_flagL_eq_one V β L κ h1
  have h2 : levChi V β (flagL L) κ⁻¹ * levChi V β (flagL L) κ = 1 := by
    have a := levFn_flag_mul (V := V) (β := β) (L := L) (isLiftFlagGroup_inv h).2.1 h.2.1
    have b := levFn_flag_mul (V := V) (β := β) (L := L) (Subgroup.one_mem _) (Subgroup.one_mem _)
    rw [mul_one, left_eq_mul] at b
    rw [← map_mul, inv_mul_cancel, map_one, b] at a
    unfold levChi
    rw [← Units.val_mul, ← a, Units.val_one]
  rw [inv_eq_of_mul_eq_one_right h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem integral_act (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (g : G0 L.Pg L.r) {φ ψ : GA D V → ℂ}
    (hφ : ∀ γ ∈ GQ V, ∀ x, φ (γ * x) = φ x) (hψ : ∀ γ ∈ GQ V, ∀ x, ψ (γ * x) = ψ x) (ht : HasType V β (flag1L L) ψ) :
    ∫ x in 𝓕, star (actG0 V β L g φ x) * ψ x ∂μ = ∫ x in 𝓕, star (φ x) * actG0 V β L g⁻¹ ψ x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  by_cases hk : ∃ κ, IsLevelLift V β L g κ
  · have hκ := hk.choose_spec
    have h1 := level_action_spec ht ⟨_, isLiftFlagGroup_inv hκ⟩ _ (isLiftFlagGroup_inv hκ)
    have h2 := (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * actG0 V β L g⁻¹ ψ x) hk.choose h𝓕
      fun γ hγ x => by rw [h1, h1, mul_assoc γ, hφ γ hγ, hψ γ hγ]).2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun x => ?_)
    show star (actG0 V β L g φ x) * ψ x = star (φ (x * hk.choose)) * actG0 V β L g⁻¹ ψ (x * hk.choose)
    rw [h1, levChi_inv hκ, mul_inv_cancel_right, actG0, dite_eq_left hk, star_mul']
    ring
  · have hk' : ¬ ∃ κ, IsLevelLift V β L g⁻¹ κ := fun ⟨κ, h⟩ => hk ⟨κ⁻¹, by simpa using isLiftFlagGroup_inv h⟩
    simp [actG0, dif_neg hk, dif_neg hk']

theorem ipM_gaL (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, c g⁻¹ = star (c g)) {X Y : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)))
    (hY : Y ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    ipM M μ 𝓕 (postOn M (gaL V β L eG c) X) Y = ipM M μ 𝓕 X (postOn M (gaL V β L eG c) Y) := by
  have hs := GlobalTheory.MultFinite.schurMult (θ := θ) (M := M) (J := (levG V β (flag1L L) : Set (GA D V))) (χ := levChi V β (flag1L L))
    hP μ 𝓕 hθ hμ h𝓕
  have ha : ∀ g, ∀ Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)),
      postOn M (actL V β L g) Z ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    fun g Z hZ => GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L g Z hZ _ fun _ => rfl
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D _ _ M)
  have h1 := (ipM_spec M μ 𝓕 _ _ (hs _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hX) _ hY) v v).2
  have h2 := (ipM_spec M μ 𝓕 _ _ (hs _ hX _ (GlobalTheory.ProjectedLift.postOn_gaL_mem hθ eG c hY)) v v).2
  refine mul_right_cancel₀ hv (h1.symm.trans (Eq.trans ?_ h2))
  have e1 : ∀ x, star (postOn M (gaL V β L eG c) X v x) * Y v x =
      ∑ g, c g⁻¹ * (star (actG0 V β L (eG g) (X v) x) * Y v x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
      star_mul', Finset.sum_mul, hc, mul_assoc]
    rfl
  have e2 : ∀ x, star (X v x) * postOn M (gaL V β L eG c) Y v x =
      ∑ g, c g⁻¹ * (star (X v x) * actG0 V β L (eG g)⁻¹ (Y v) x) := fun x => by
    simp only [gaL, postOn_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    rw [Equiv.inv_apply, inv_inv, map_inv, inv_inv, mul_left_comm]
    rfl
  have hX' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ X).1 hX
  have hY' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ Y).1 hY
  simp only [e1, e2]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_const_mul, integral_const_mul, integral_act hμ h𝓕 _ (hX'.aut v).left (hY'.aut v).left
      (GlobalTheory.hasType_of_mem_mult θ M β _ Y hY v)]
  · exact fun g _ => ((hs _ hX _ (ha (eG g)⁻¹ _ hY)).choose_spec v v).1.const_mul _
  · exact fun g _ => ((hs _ (ha (eG g) _ hX) _ hY).choose_spec v v).1.const_mul _

end Act

theorem eC_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_record) (g : G) :
    RealDat.eC (A := A) D.what₂.embLL g⁻¹ = star (RealDat.eC (A := A) D.what₂.embLL g) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have : Finite (G0g D.nd) := Finite.of_equiv G eR.toEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  unfold RealDat.eC
  rw [h, h, map_inv]
  exact GlobalTheory.RowLev.GroupAlgPos.isSA_central _ h2 (fun a => (Subalgebra.mem_center_iff.1 h1 a).symm) _

end GlobalTheory.ProjectorAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsoPairToTermSymm
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)


set_option maxHeartbeats 4000000 in
theorem isoPair_toTerm (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact ((Eq.refl (eRT Z Y u u' s.toTerm)) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_toTerm_symm (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := (by with_unfolding_all exact ((Eq.refl ((eTT Z Y u u').symm s).toTerm) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_row (a b : TT Y u u') :
    rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' a) =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' b) ↔
      rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b := (by with_unfolding_all exact ((Iff.rfl : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b ↔ _) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_row_symm (a b : TT (reY Z Y) (wd Z u) (wd Z u')) :
    rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm a) = rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm b) ↔
      rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) a =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) b := by
  have := isoPair_row Z Y u u' ((eTT Z Y u u').symm a) ((eTT Z Y u u').symm b)
  simpa only [Equiv.apply_symm_apply] using this.symm


set_option maxHeartbeats 4000000 in
theorem isoPair_s0T (a b : TT Y u u') : s0T (eTT Z Y u u' a) (eTT Z Y u u' b) = s0T a b := (by with_unfolding_all exact (
  (Eq.refl (s0T a b)) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_lift (a b : TT Y u u') : liftScalar (eTT Z Y u u' a) (eTT Z Y u u' b) ↔ liftScalar a b := (by exact (Iff.rfl : liftScalar a b ↔ liftScalar a b))

def isoPairFib (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) where
  toFun s := ⟨eTT Z Y u u' s.1, by rw [isoPair_toTerm, s.2]⟩
  invFun s := ⟨(eTT Z Y u u').symm s.1, by rw [isoPair_toTerm_symm, s.2, Equiv.symm_apply_apply]⟩
  left_inv s := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv s := Subtype.ext (Equiv.apply_symm_apply _ _)

def isoPairE : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') where
  toFun q := ⟨(eRT Z Y u u' q.1.1, eRT Z Y u u' q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    exact ⟨isoPairFib Z Y u u' _ s₁, isoPairFib Z Y u u' _ s₂, (isoPair_row Z Y u u' _ _).2 hs⟩⟩
  invFun q := ⟨((eRT Z Y u u').symm q.1.1, (eRT Z Y u u').symm q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    refine ⟨⟨(eTT Z Y u u').symm s₁.1, by rw [isoPair_toTerm_symm, s₁.2]⟩,
      ⟨(eTT Z Y u u').symm s₂.1, by rw [isoPair_toTerm_symm, s₂.2]⟩, (isoPair_row_symm Z Y u u' _ _).2 hs⟩⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)


set_option maxHeartbeats 4000000 in
theorem rp_iso_pair : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y))
    (u u' : D.what₂.Word), ∃ e : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u'), ∀ q, eRT Z Y u u' q.1.1 = (e q).1.1 ∧
      eRT Z Y u u' q.1.2 = (e q).1.2 ∧ s0T q.l1 q.l2 = s0T (e q).l1 (e q).l2 ∧
      (liftScalar q.l1 q.l2 ↔ liftScalar (e q).l1 (e q).l2) ∧
      pvR h u u' q = pvR h' (wd Z u) (wd Z u') (e q) := by
  intro D Z X Y h h' u u'
  refine ⟨isoPairE Z Y u u', fun q => ⟨rfl, rfl, ?_⟩⟩

  set a := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l1 with ha
  set b := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l2 with hb
  have hA : (isoPairE Z Y u u' q).l1 = eTT Z Y u u' a := by simp [a]
  have hB : (isoPairE Z Y u u' q).l2 = eTT Z Y u u' b := by simp [b]
  have h1 : q.l1.toTerm = q.1.1 := q.2.choose.2
  have h2 : q.l2.toTerm = q.1.2 := q.2.choose_spec.choose.2
  have hr : rowOf Y.TR (Y.cs u) (Y.cs u') q.l1 = rowOf Y.TR (Y.cs u) (Y.cs u') q.l2 := q.2.choose_spec.choose_spec
  have e1 : (isoPairE Z Y u u' q).l1.toTerm = eRT Z Y u u' q.1.1 := (isoPairE Z Y u u' q).2.choose.2
  have e2 : (isoPairE Z Y u u' q).l2.toTerm = eRT Z Y u u' q.1.2 := (isoPairE Z Y u u' q).2.choose_spec.choose.2
  have er := (isoPairE Z Y u u' q).2.choose_spec.choose_spec
  have ha1 : a.toTerm = q.1.1 := by rw [isoPair_toTerm_symm]; erw [e1]; simp
  have hb1 : b.toTerm = q.1.2 := by rw [isoPair_toTerm_symm]; erw [e2]; simp
  have hab : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b :=
    (isoPair_row_symm Z Y u u' _ _).2 er
  obtain ⟨hs, hl⟩ := h.pairIndep u u' q.l1 q.l2 a b (h1.trans ha1.symm) (h2.trans hb1.symm) hr hab
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, hB, isoPair_s0T]; exact hs
  · rw [hA, hB, isoPair_lift]; exact hl
  · letI := h.fibFT q.1.1
    letI := h.fibFT q.1.2
    letI := h'.fibFT (eRT Z Y u u' q.1.1)
    letI := h'.fibFT (eRT Z Y u u' q.1.2)
    unfold pvR
    refine Fintype.sum_equiv ((isoPairFib Z Y u u' q.1.1).prodCongr (isoPairFib Z Y u u' q.1.2)) _ _
      fun r => ?_
    exact (by with_unfolding_all exact ((Eq.refl (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1
        then inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else (0 : ℂ))) :))

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumEqOfFramesInnerConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.FrameIsot

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

theorem iSup_le_of_intertwine (σ₁ σ₂ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (T : S →ₗ[ℂ] S) (hT : Function.Surjective T) (hc : ∀ g s, σ₁ g (T s) = T (σ₂ g s)) :
    (⨆ f ∈ homInto σ₁ ρ C, LinearMap.range f) ≤ ⨆ f ∈ homInto σ₂ ρ C, LinearMap.range f := by
  refine iSup₂_le fun f hf => ?_
  have hm : f ∘ₗ T ∈ homInto σ₂ ρ C := by
    refine ⟨fun s => hf.1 (T s), fun g s => ?_⟩
    show f (T (σ₂ g s)) = ρ g (f (T s))
    rw [← hc]; exact hf.2 g (T s)
  have hr : LinearMap.range (f ∘ₗ T) = LinearMap.range f := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hT, Submodule.map_top]
  exact hr ▸ le_iSup₂_of_le (f ∘ₗ T) hm le_rfl

end GlobalTheory.FrameIsot

open GlobalTheory.FrameIsot in
theorem GlobalTheory.FrameIsot.iSup_homInto_frame_conj : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n) (Φ : GfC Y ≃ₜ* GfC W) (h : Formalism.AUTREP.GAf D.host.E n), (∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC W) X) (C : Submodule ℂ X) (π : Formalism.L2.NG.FinTyp D.host.E n), (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (ρ.comp Φ.toMulEquiv.toMonoidHom) C, LinearMap.range f) = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PW).symm.toMonoidHom) ρ C, LinearMap.range f := by
  intro D Y W n PY PW Φ h hΦ X _ _ ρ C π
  rw [GlobalTheory.PartDims.homInto_comp]
  set eY := GlobalTheory.KapIsot.eqv PY
  set eW := GlobalTheory.KapIsot.eqv PW
  have key : ∀ κ', eY.symm (Φ.toMulEquiv.symm (eW κ')) = h⁻¹ * κ' * h := by
    intro κ'
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have := hΦ (h⁻¹ * κ' * h)
    rw [show h * (h⁻¹ * κ' * h) * h⁻¹ = κ' by group] at this
    exact this.symm
  have hW : ∀ κ', eW.symm (eW κ') = κ' := fun κ' => MulEquiv.symm_apply_apply _ _
  apply le_antisymm
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h⁻¹) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h s, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) _ = GlobalTheory.OccRowVec.finRep π h⁻¹ (GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h⁻¹ s, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) _ = GlobalTheory.OccRowVec.finRep π h (GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.PinsCoord

theorem extTo_basis {E : Type} [Field E] (n N : ℕ) (a : Fin n) (b : Fin N) (h : (a:ℕ) = b) : DiagSp.extTo (E := E) n N (Pi.basisFun E (Fin n) a) = Pi.basisFun E (Fin N) b := by
  funext i
  simp only [Pi.basisFun_apply]
  show (if h : (i:ℕ) < n then (Pi.single a (1:E) : Fin n → E) ⟨i, h⟩ else 0) = _
  by_cases e : i = b
  · subst e
    have : (i:ℕ) < n := h ▸ a.2
    rw [dite_eq_left this, show (⟨i, this⟩ : Fin n) = a from Fin.ext h.symm]; simp
  · rw [Pi.single_eq_of_ne e]
    split_ifs with h1
    · exact Pi.single_eq_of_ne (fun e' => e (Fin.ext (by rw [← h, ← e']))) _
    · rfl

end GlobalTheory.Mem.Col2.PinsCoord
end

