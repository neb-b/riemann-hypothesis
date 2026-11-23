module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031

@[expose] public section

noncomputable section

namespace GlobalTheory.ResLoc

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie
  GlobalTheory.SplitRead GlobalTheory.XiOver Formalism.L2.Host

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts GlobalTheory.ParamRep

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hecke_of_loc (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    {w : PlE H} (e3 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w = A.locV i P w)
    (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

theorem continuous_of_iota (i : N.Loc) {Y : Type} [TopologicalSpace Y] (u : Y → N.O i)
    (hd : Continuous fun y => iotaOQ N A i (u y)) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  obtain ⟨δ, hδ, hk⟩ := GlobalTheory.XiOver.mem_pow_of_norm_lt N A i k
  have hcd : ∀ᶠ x in nhds g, ‖iotaOQ N A i (u x) - iotaOQ N A i (u g)‖ < δ :=
    (Metric.tendsto_nhds.1 (hd.tendsto g) δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx
  filter_upwards [hcd] with x hx
  apply hk
  rw [map_sub]
  exact hx

private theorem diagM_ss_local {Γ k : Type} [Group Γ] [Field k] :
    ∀ {t : ℕ} (χ : Fin t → Γ →* kˣ), IsSSRep (GlobalTheory.SSComplement.diagM χ).toHomUnits := by
  have scalar_ss {a : ℕ} (ρ : Γ →* GL (Fin a) k) (c : Γ → k)
      (h : ∀ g v, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v = c g • v) : IsSSRep ρ := by
    intro W _
    obtain ⟨W', hW'⟩ := W.exists_isCompl
    exact ⟨W', fun g v hv => by rw [h]; exact W'.smul_mem _ hv, hW'⟩
  intro t
  induction t with
  | zero =>
    intro χ
    exact scalar_ss _ (fun _ => 0) fun g v => funext fun c => c.elim0
  | succ t ih =>
    intro χ
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod
      (ρ₁ := (GlobalTheory.SSComplement.diagM fun c : Fin t => χ (Fin.castAdd 1 c)).toHomUnits)
      (ρ₂ := (GlobalTheory.SSComplement.diagM fun c : Fin 1 => χ (Fin.natAdd t c)).toHomUnits)
      ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) (ih _)
      (scalar_ss _ (fun g => ((χ (Fin.last t) g : kˣ) : k)) fun g v => ?_)
    · show _ = _
      ext i <;> simp [GlobalTheory.SSComplement.diagM, Matrix.mulVec_diagonal, LinearMap.funLeft]
    · funext c
      obtain rfl : c = 0 := Subsingleton.elim _ _
      change (Matrix.diagonal fun c : Fin 1 => ((χ (Fin.natAdd t c) g : kˣ) : k)).mulVec v 0 = _
      exact Matrix.mulVec_diagonal _ _ _

theorem lattice_of_point (hLaw : GlobalTheory.ThetaExh.ParamLaws N A) (hO : Formalism.MainNotions.SumRepresentations.At.OLarge N A)
    (hXi : ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ,
      Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
      ∀ w : PlE H, w ∉ placesOver H.E (N.l i) →
        (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
        ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
          IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
          A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) =
            {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)})
    (a : N.Loc) (x : N.X a) (P : A.AV a) (hP : A.ptV a P = some x) (π : A.CG R.r)
    (hloc : ∀ w, IsSplitPl H w → A.locV a P w = GlobalTheory.ThetaExh.liftPar N A a w (A.locG π w))
    (hun : ∀ w, (∀ k, w ∉ placesOver H.E (H.g k)) → A.unr (A.locG π w))
    (ρ₀ : G H.E N.Om →* GL (Fin R.r) (Qbar (N.l a)))
    (hc0 : Continuous fun g => ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a)))) (hs0 : IsSSRep ρ₀)
    (hfr : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) → ∀ (B : ValuationSubring N.Om)
      (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      (((ρ₀ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom).charpoly =
        galPol A (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))) :
    ∃ ρ : G H.E N.Om →* GL (Fin R.r) (N.O a), IsRepOfSig N A a [⟨R.r, π, 1⟩] ρ := by
  haveI : IsGalois H.E N.Om := {}
  obtain ⟨ξ, hξc, hξ⟩ := hXi a
  have hιc : Continuous (iotaOQ N A a) := GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A a
  have hcomp : iotaO N A a = (A.iotaQC a).toRingHom.comp (iotaOQ N A a) := rfl
  have hinj : Function.Injective (Polynomial.map (A.iotaQC a).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC a).injective

  let R1 := Formalism.MainNotions.SumRepresentations.At.twGL ρ₀ ((Units.map (iotaOQ N A a).toMonoidHom).comp ξ)
  have hR1 : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) =
      iotaOQ N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) :=
    fun g => coe_twGL _ _ g
  have hR1c : Continuous fun g => ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) := by
    simp only [hR1]
    exact (hιc.comp hξc).smul hc0
  have hR1C : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom =
      iotaO N A a ((ξ g : (N.O a)ˣ) : N.O a) •
        ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom := by
    intro g
    rw [hR1, map_smul_matrix]
    rfl
  have hfin := placesOver_finite_joint_conditions_zpowers H.E (N.l a) (N.lPrime a).out.ne_zero

  let χ : Fin R.t → G H.E N.Om →* (Qbar (N.l a))ˣ := fun c =>
    (Units.map (iotaOQ N A a).toMonoidHom).comp (N.chi a ((c : ℕ) + 1))
  let Rq : G H.E N.Om →* GL (Fin (R.r + R.t)) (Qbar (N.l a)) :=
    (GlobalTheory.SSComplement.blockM finSumFinEquiv R1 (GlobalTheory.SSComplement.diagM χ).toHomUnits).toHomUnits
  have hRq : ∀ g, ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a))) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) 0 0
      (Matrix.diagonal fun c : Fin R.t => iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := fun g => rfl
  have hRqc : Continuous fun g => ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a))) := by
    simp only [hRq]
    refine Continuous.matrix_reindex ?_ _ _
    refine Continuous.matrix_fromBlocks hR1c continuous_const continuous_const ?_
    exact Continuous.matrix_diagonal (continuous_pi fun c => hιc.comp (N.chi_cont a _))
  have hRqs : IsSSRep Rq :=
    GlobalTheory.SSComplement.blockM_ss _ _ _ (isSSRep_twGL _ _ hs0) (diagM_ss_local χ)
  have hq : Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ N A a x Rq := by
    refine ⟨hRqc, hRqs, fun v hso B g hBv hg => ?_⟩
    have h4 : A.unr (A.locG π v) := hun v fun k hk => hso.2.2.1 ((N.S_def a v).2 ⟨by
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk), hso.2.1⟩)
    have h5 : A.unr (A.locG (A.tw π A.etaTinv) v) := by
      rw [A.locG_tw]
      exact A.unr_char _ _ (A.locG_dim _ _) h4 (A.etaTinv_def v).1
    have h1 := hso.2.1
    have e3 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A a]) A.etaTinv) v = A.locV a P v := by
      rw [GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift N A hLaw, hloc v hso.1]
      congr 1
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    apply hinj
    rw [Polynomial.map_map, ← hcomp]
    refine Eq.trans (congrArg (Polynomial.map (A.iotaQC a).toRingHom)
      ((congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _))) ?_
    symm
    rw [Polynomial.map_mul, ← Matrix.charpoly_map, hR1C g,
      hecke_of_loc N A a x π P hP e3 hso h5 hBv hg,
      galPol_twist N A π h4 _ ((hξ v h1).2 B g hBv hg),
      charpoly_smul_of_prod _ _ _ (hfr v h1 h4 B g hBv hg), prod_Icc_eq_fin, Polynomial.map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  obtain ⟨rf, Pm, hPm⟩ := hO a x Rq hq
  have hval : ∀ g, ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a) =
      ((Pm⁻¹ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a))) *
        (show Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a)) from
          ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a)))) *
        ((Pm : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a))) := fun g => congrArg Units.val (hPm g)
  have hrc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)) := by
    have hc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a) := by
      simp only [hval]
      exact (continuous_const.mul hRqc).mul continuous_const
    exact continuous_pi fun p => continuous_pi fun q => continuous_of_iota N A a _ (hc.matrix_elem p q)
  have hrs : IsSSRep (mapRep (algebraMap (N.O a) (Kf N a)) rf) := by
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_mapRep (A.iotaQ a) _ ?_
    rw [GlobalTheory.RowRepOcc.mapRep_mapRep]
    exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_conj (ρ := (Rq : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l a)))) Pm⁻¹
      (fun g => hPm g) hRqs

  haveI : CharZero (Qbar (N.l a)) := (RingHom.charZero_iff (A.iotaQC a).toRingHom.injective).2 inferInstance
  haveI : CharZero (Kf N a) := (RingHom.charZero_iff (A.iotaQ a).injective).2 inferInstance
  have hkey' : ∀ g, (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly *
        ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
    intro g
    rw [← Matrix.charpoly_map, hval g, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    exact (congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _)
  obtain ⟨ρ', hρc, hρs, hρp⟩ := GlobalTheory.LatticeComplement.exists_lattice_complement (G H.E N.Om) (N.O a) (Kf N a)
    R.r R.t (rf) (fun c : Fin R.t => N.chi a ((c : ℕ) + 1)) hrc hrs
    ⟨Qbar (N.l a), inferInstance, A.iotaQ a, R1, hkey'⟩
  have hcan : ∀ g, ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly := by
    intro g
    have e1 : (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
        ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) *
          ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
      have := congrArg (Polynomial.map (iotaOQ N A a)) (hρp g)
      rw [Polynomial.map_mul, Polynomial.map_prod] at this
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hne : (∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))) ≠ 0 :=
      (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _).ne_zero
    exact mul_right_cancel₀ hne (e1.symm.trans (hkey' g))
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹, ?_, ?_, ?_⟩
  · have e : (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))) =
        fun g => ((ξ g⁻¹ : (N.O a)ˣ) : N.O a) • ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)) := by
      funext g
      rw [coe_twGL, MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (hξc.comp continuous_inv).smul hρc
  · rw [mapRep_twGL]
    exact isSSRep_twGL _ _ hρs
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hBw hσ
    have iso : isoLoc N A [⟨R.r, π, 1⟩] w = A.locG π w := by
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    rw [iso]
    have h0 := hfr w h1 h2 B σ hBw hσ
    have c1 : (((ρ' σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).map (iotaO N A a)).charpoly =
        (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map fun α => X - C α).prod := by
      rw [Matrix.charpoly_map, hcomp, ← Polynomial.map_map, hcan σ, ← Matrix.charpoly_map, hR1C σ]
      exact charpoly_smul_of_prod _ _ _ h0
    have c2 := charpoly_smul_of_prod _ (iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) _ c1
    have huv : iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a) * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a) = 1 := by
      rw [← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
      simp
    have hL : ((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map
          (· * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) =
        A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl fun α _ => ?_).trans (Multiset.map_id _)
      show α * _ * _ = α
      rw [mul_assoc, huv, mul_one]
    rw [← Matrix.charpoly_map, coe_twGL, map_smul_matrix, c2, hL]
    rfl

end GlobalTheory.ResLoc

end
