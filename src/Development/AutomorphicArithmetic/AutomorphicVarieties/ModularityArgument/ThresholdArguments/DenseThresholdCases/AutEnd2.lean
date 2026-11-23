module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutEnd2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Across2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
open UpperTheory.V.Z.Win UpperTheory.V.Z
open scoped Matrix
private theorem detAlg (H : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hW : Continuous W) {M : ℕ} (hM : 1 ≤ M) (hχ : Af.KillsMu M (Matrix.GeneralLinearGroup.det.comp W)) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
  have : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω M
  let k := Fintype.card (ZMod M)ˣ
  have hk : 0 < k := Fintype.card_pos
  have hpow (s : G ℚ Ω) : (Matrix.GeneralLinearGroup.det.comp W s) ^ k = 1 := by
    rw [← map_pow]
    refine hχ _ fun ζ hζ => ?_
    have hfix := hμ.autToPow_spec ℚ (s ^ k)
    dsimp [k] at hfix
    rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at hfix
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, ← hfix]
  refine (_root_.UpperTheory.V.Af.algOfCyc_s H ℚ Ω l ι).1 _ (Matrix.GeneralLinearGroup.continuous_det.comp hW) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩
private theorem polTwo {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)) (c : G ℚ Ω)
    (hc : Sd.IsCC c) : Af.Sol.Pol ι (W.comp (Base.galEmb ℚ K Ω)) := by
  let J : GL (Fin 2) (Qbar l) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  have hJ (A : Matrix (Fin 2) (Fin 2) (Qbar l)) :
      Aᵀ * J.val * A = A.det • J.val := by
    change Aᵀ * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
  refine ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, J * W c⁻¹, h, Ws.auSign _, hc, fun s s' hconj => ?_⟩
  let t := Base.galEmb ℚ K Ω s
  have hs' : Base.galEmb ℚ K Ω s' = c * t * c⁻¹ := hconj
  have hmul : W c⁻¹ * W (c * t * c⁻¹) = W t * W c⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hval : (W c⁻¹).val * (W (c * t * c⁻¹)).val = (W t).val * (W c⁻¹).val :=
    congrArg Units.val hmul
  change (W t).valᵀ * (J * W c⁻¹).val * (W (Base.galEmb ℚ K Ω s')).val =
    (W t).val.det • (J * W c⁻¹).val
  rw [hs', Units.val_mul, ← Matrix.smul_mul, ← hJ]
  simp only [Matrix.mul_assoc, hval]
open Matrix in
theorem UpperTheory.V.Z.Win.Dn.autEnd2_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hPot : Dn.PotTwo) (hIne : Dn.Ine2) :
    RankTwoAutomorphyDescendsFromAbelianCMToRat → _root_.UpperTheory.V.Z.Win.RR.AutNewformA → Sd.TwC → Sd.AlgCyc → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)} (k : GalLink D.η D.Ψ D.cc g₁ B M L Φ) [CharP (ResidueField c.O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → B.valuation (l : Ω) < 1 → LinkHyp c N e D.η D.cc B M →
      ∀ (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ), Sd.IsAlgChar ι ka → _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka → _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι := by
  intro hDown hNew hTw hAlg Ω _ _ _ K _ _ _ l hl c N _ e ψ D g₁ B M L _ _ _ _ Φ k _ C₀ hok hM hB hLk ι ka hka hA
  intro A _ _ r hr hII h11 W hW _
  obtain ⟨hcc, hηc, -, hηl, -, -, h2, hcm, -⟩ := dat_facts D
  obtain ⟨hk1, hk2, hk3, -⟩ := eta_killsMu D
  have := k.ab
  have := hcm
  have : IsAlgClosure K Ω := Th.Db.algClo K Ω
  have : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  have : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  obtain ⟨_, hloc, hentry⟩ := UpperTheory.V.Th.End3.sub_facts c A
  have : IsLocalHom (algebraMap c.O A) := hloc
  have : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  have hW' : ∀ g ∈ D.η.ker, (W g).val = (corner (r g).mat).map A.val := hW
  have hblk : Block D.η r := fun g hg a b h => Subtype.ext (hII.1 g hg a b h)
  have hirr : MatIrr D.η.ker fun g => (W g).val := fun V hV => hII.2 V fun g hg v hv => by
    have : (W g).val.mulVec v ∈ V := hV g hg v hv
    rwa [hW g hg] at this
  have hopen : IsOpen (D.η.ker : Set (G ℚ Ω)) := hηl.isOpen_fiber 1
  have hcont : Continuous W := by
    have hcorner : Continuous fun g => (corner (r g).mat).map A.val := by
      refine continuous_matrix fun i j => hentry _ (fun g => (r g).mat (![0, 2] i) (![0, 2] j)) fun n => ?_
      exact (hr.cont n).comp fun X => X (![0, 2] i) (![0, 2] j)
    have hval : Continuous fun g => (W g).val := by
      refine continuous_of_continuousAt_one ((Units.coeHom _).comp W) (hcorner.continuousAt.congr ?_)
      filter_upwards [hopen.mem_nhds D.η.ker.one_mem] with g hg
      exact (hW' g hg).symm
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    simp only [← map_inv]
    exact hval.comp continuous_inv
  have hdW : ∀ g ∈ D.η.ker, (W g).val.det = A.val (corner (r g).mat).det := fun g hg => by
    rw [hW' g hg, AlgHom.map_det]
    rfl
  have hred (g : G ℚ Ω) :
      residue A ((r g).mat 0 0) = residue A (algebraMap c.O A (D.Ψ g)) ∧
      residue A ((r g).mat 2 2) = residue A (algebraMap c.O A ((D.Ψ g)⁻¹ : c.Oˣ)) ∧
      residue A ((r g).mat 0 2) = 0 := by
    have h0 := (residue_eq_zero_iff _).2 (hr.red.red g 0 0)
    have h1 := (residue_eq_zero_iff _).2 (hr.red.red g 2 2)
    have h2 := (residue_eq_zero_iff _).2 (hr.red.red g 0 2)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0 h1 h2
    refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩ <;> simp [GG.mat, tor_val, wt1]
  have hdet : ∀ g ∈ D.η.ker, (W g).val.det = 1 := fun g hg => by
    obtain ⟨s1, s2⟩ := mat_gstar r D.cc g hr.norm.atc ((hr.red.mult _).trans hηc) ((hr.red.mult _).trans hg)
    have e1 := hdW _ (show gstar D.cc g ∈ D.η.ker from (hr.red.mult _).symm.trans s2)
    have hstar (X : Matrix (Fin 3) (Fin 3) A) :
        (corner (Jmat A 3 * Xᵀ * Jmat A 3)).det = (corner X).det := by
      have e : ∀ Y : Matrix (Fin 3) (Fin 3) A, (corner Y).det = Y 0 0 * Y 2 2 - Y 0 2 * Y 2 0 := fun Y => by
        rw [Matrix.det_fin_two]; rfl
      rw [e, e]
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, mul_comm]
    rw [s1, hstar, ← hdW g hg] at e1
    have e2 : Matrix.GeneralLinearGroup.det (W (gstar D.cc g)) * Matrix.GeneralLinearGroup.det (W g) = 1 := by
      have := congrArg (Matrix.GeneralLinearGroup.det.comp W) hcc
      rw [map_mul, map_one] at this
      show (Matrix.GeneralLinearGroup.det.comp W) (D.cc * g⁻¹ * D.cc) * (Matrix.GeneralLinearGroup.det.comp W) g = 1
      rw [map_mul, map_mul, map_inv, mul_right_comm _ _⁻¹, this, one_mul, inv_mul_cancel]
    have e3 : (W (gstar D.cc g)).val.det * (W g).val.det = 1 := congrArg Units.val e2
    rw [e1, hdW g hg, ← map_mul] at e3
    rw [hdW g hg]
    have hd : (corner (r g).mat).det ^ 2 = 1 := (sq _).trans (Subtype.ext e3)
    obtain ⟨a, b, c₀⟩ := hred g
    have hres : residue A (corner (r g).mat).det = 1 := by
      have : (corner (r g).mat).det = (r g).mat 0 0 * (r g).mat 2 2 - (r g).mat 0 2 * (r g).mat 2 0 := by
        rw [Matrix.det_fin_two]; rfl
      rw [this, map_sub, map_mul, map_mul, a, b, c₀, ← map_mul, ← map_mul, Units.mul_inv]
      simp
    rcases mul_self_eq_one_iff.1 ((sq _).symm.trans hd) with hpos | hneg
    · rw [hpos, map_one]
    · exfalso
      have htwo := (h2.map ((residue A).comp (algebraMap c.O A))).ne_zero
      rw [hneg, map_neg, map_one] at hres
      rw [map_ofNat] at htwo
      exact htwo (by linear_combination -hres)
  have hcyc : Af.IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) :=
    ⟨_, Matrix.GeneralLinearGroup.det.comp W, hk2, fun s hs => Units.ext (hdet s (hk1 s hs)), by simp⟩
  obtain ⟨hg, eg⟩ := k.g0
  have hηg : D.η g₁ = 1 := by
    have h := k.del ⟨g₁, hg⟩
    rw [eg] at h
    exact h.symm.trans Φ.g0.2
  have hsq (g : G ℚ Ω)
      (ht : (r g).mat 0 0 + (r g).mat 2 2 = 0) : ((barChar c.O D.Ψ g : (ResidueField c.O)ˣ) : ResidueField c.O) ^ 2 = -1 := by
    obtain ⟨a, b, -⟩ := hred g
    have e := congrArg (residue A) ht
    rw [map_add (f := _), a, b, ← map_add (f := _), ← map_add (f := _), map_zero, residue_eq_zero_iff, mem_maximalIdeal, map_mem_nonunits_iff,
      ← mem_maximalIdeal, ← residue_eq_zero_iff, map_add] at e
    have e2 : residue c.O (D.Ψ g) * residue c.O ((D.Ψ g)⁻¹ : c.Oˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    show residue c.O (D.Ψ g) ^ 2 = -1
    linear_combination residue c.O (D.Ψ g) * e - e2
  have hcomm (a b : G ℚ Ω) : a * b * a⁻¹ * b⁻¹ ∈ Base.galOf ℚ L Ω := by
    intro x
    have h : AlgEquiv.restrictNormalHom L (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, IsMulCommutative.is_comm.comm (AlgEquiv.restrictNormalHom L a)]
      group
    rw [← AlgEquiv.restrictNormal_commutes]
    exact congrArg (fun s : L ≃ₐ[ℚ] L => algebraMap L Ω (s x)) h
  have irreducibleOn {Γ κ k : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] [Field k] (W : Γ →* GL (Fin 2) κ)
      (U H : Subgroup Γ) [H.Normal] (hab : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H) (hU : MatIrr U fun g => (W g).val)
      (χ : Γ →* kˣ) (ht : ∀ g ∈ U, (W g).val.trace = 0 → (χ g : k) ^ 2 = -1) (h : Γ) (hh : h ∈ H) (hhU : h ∈ U)
      (hχ : χ h ^ 2 ≠ 1) : MatIrr H fun g => (W g).val := by
    intro V hV
    by_contra hne
    obtain ⟨φ, h1, h2, -, P, hP⟩ := exists_selfTwist (W.comp U.subtype) (H.subgroupOf U) (fun a b => hab a b)
      (fun V' hV' => hU V' fun g hg => hV' ⟨g, hg⟩ trivial) (fun hi => hne (hi V fun g hg => hV g hg))
    obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 1 := by
      by_contra hn
      push Not at hn
      exact h1 (MonoidHom.ext hn)
    have key : ∀ g : U, φ g ≠ 1 → (χ g : k) ^ 2 = -1 := fun g hg => by
      refine ht g g.2 ?_
      have e := congrArg (fun Y => ((P⁻¹ : GL (Fin 2) κ).val * Y).trace) (hP g trivial)
      simp only [] at e
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc, Units.mul_inv,
        Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at e
      by_contra h0
      exact hg (Units.ext (mul_right_cancel₀ h0 (e.trans (one_mul _).symm)))
    have e1 := key g hg
    have e2 := key (g * ⟨h, hhU⟩) (by rwa [map_mul, show φ ⟨h, hhU⟩ = 1 from h2 hh, mul_one])
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, mul_pow, e1] at e2
    refine hχ (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination -e2
  have irreducibleOfRange {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (W : Γ →* GL (Fin 2) k) (f : Γ' →* Γ) (H : Subgroup Γ)
      (hH : H ≤ f.range) (h : MatIrr H fun g => (W g).val) : Af.IsIrr (W.comp f) :=
    ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun V _ hV => h V fun g hg v hv => by
      obtain ⟨s, rfl⟩ := hH hg
      exact hV s v hv⟩
  have hirrL : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) := by
    refine irreducibleOfRange W _ _ (Base.range_galEmb ℚ L Ω).ge (irreducibleOn W D.η.ker (Base.galOf ℚ L Ω) hcomm hirr
      (barChar c.O D.Ψ) (fun g hg ht => hsq g (Subtype.ext ?_)) g₁ (k.gal ▸ ⟨hg, hηg⟩) hηg ?_)
    · rw [hW g hg, Matrix.trace_fin_two] at ht
      exact ht
    · have h := k.psi ⟨g₁, hg⟩
      rw [eg] at h
      exact h ▸ hok.baseSubgroup_spec
  obtain ⟨ρ, r1, r2, r3⟩ := exists_nrep2 k hok hM hcc r hr hblk
  obtain ⟨⟨π, p1, -, p3⟩, hWit⟩ := _root_.UpperTheory.GalN.V.csdN'_alt H.toClassicalTheorems (by norm_num) <| hA A ρ r1 r3 (W.comp (Base.galEmb ℚ L Ω)) (fun s => by
    rw [r2]
    exact hW' _ (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2) hirrL
  have twist_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
      Af.tw (Af.tw r χ) χ⁻¹ = r := by
    refine MonoidHom.ext fun s => Units.ext ?_
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
  have hC := hTw L Ω l ι 2 _ ka⁻¹ ((hAlg L Ω l ι).2.2 ka hka) ⟨π, p1, p3⟩
  rw [twist_inv] at hC
  have hR := hDown L Ω l ι W hcont hcyc hirrL
    ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩ hC
  have hΨ : ∀ g, Chr.dirG ℚ Ω ψ g = 1 → D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) := fun g hg => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (Base.chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [hg, mul_one, map_zpow]
    rfl
  suffices hfl : Af.IsFlagOn W ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp ((D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) ⊓ Ine (F := ℚ) B).subtype) by
    have hψopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := by
      have hfin : {ζ : Ω | ζ ^ N = 1}.Finite := by
        classical
        refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
        simpa [Polynomial.mem_nthRoots (NeZero.pos N)] using hζ
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
      · simp only [Set.mem_iInter]
        exact fun ζ _ => Subgroup.one_mem _
      · simp only [Set.mem_iInter] at hs
        exact hk3 s fun ζ hζ => hs ζ hζ
    have hop := hopen.inter hψopen
    have hWL := hWit (Af.Bc.irrBasic.2 _ _ _ _ _ (hcont.comp (Af.continuous_restrictScalarsHom ℚ L Ω)) hka.1)
    have hirrQ := irreducibleOfRange W (MonoidHom.id _) _ (fun g _ => ⟨g, rfl⟩) hirr
    obtain ⟨f, hf⟩ := _root_.UpperTheory.V.Z.Win.Dn.nw' hNew Ω l ι e D.gd.e_pos W hcont hirrQ hR
      ⟨hcyc, L, _, _, _, inferInstance, _, hirrL, ⟨D.η, D.cc, D.conj, hηc, fun s => (k.gal.le (Base.galEmb_mem ℚ L Ω s)).2⟩, ka, hka, hWL⟩
      B hB _ hop hfl
    refine ⟨⟨f, hf⟩, ?_⟩
    have hQ0 : IsAutomorphicOverImagQuad ι W := _root_.UpperTheory.GalN.V.newformAut0_alt H.toClassicalTheorems _ (by have := D.gd.e_pos; omega) f l Ω ι W _ hf
    have hP := hPot Ω l e D.gd.e_pos W B hB _ hop inferInstance hfl
    have hFl : Flagged W := fun v hv A' hA' => (hP v hv A' hA').imp fun _ x => x.1
    have hI : IneAb W := hIne Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker hopen W hW
    obtain ⟨hc', art, χ, a, h'⟩ := (hAlg L Ω l ι).2.2 ka hka
    have h1 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt H.toClassicalTheorems ⟨χ, hc', art, a, h'⟩ hc' hWL
    rw [twist_inv] at h1
    obtain ⟨_, _⟩ := Th.Db.algKL K L Ω (D.η_ker ▸ (k.gal ▸ inf_le_right : Base.galOf ℚ L Ω ≤ D.η.ker))
    obtain ⟨_, hsol⟩ := Th.Db.galKL K L k.ab
    have i2 : Af.IsIrr ((W.comp (Base.galEmb ℚ K Ω)).comp (Base.galEmb K L Ω)) := hirrL
    have i1 : Af.IsIrr (W.comp (Base.galEmb ℚ K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 2 _).1 _ i2
    have hcK : Continuous (W.comp (Base.galEmb ℚ K Ω)) := hcont.comp (Af.continuous_restrictScalarsHom ℚ K Ω)
    have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := detAlg H hcont hk2 fun s hs => Units.ext (hdet s (hk1 s hs))
    have fl := (flagLaws ℚ Ω l 2 W).2.2.2 K
    have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ K Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.down'_alt L H hsol (by norm_num) hcK i2 (polTwo K W halg D.cc D.conj) (hQ0 hcont K D.gd.quad i1) (fl.2.1 hFl) (fl.1 hI)
        (Keep.keeps2 Ω l c N e ψ D.η D.cc g₁ B M hLk L Φ C₀ k hok A r hr hblk h11 K D.η_ker _
          fun s => hW _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))) h1
    exact _root_.UpperTheory.V.Z.Win.Dn.across2'_alt H K Ω D.gd.quad (by norm_num) hP hcont hQ0 ⟨_, halg, dual_two W⟩ hI hFl i1 hWK
  obtain ⟨h, -, hT⟩ := hr.ord
  have hinertia : ∃ s ∈ Ine (F := ℚ) B, ∀ n : ℤ, cycBar ℚ Ω l s ^ n = 1 → n = 0 := by
    have hu : IsUnit ((2 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hl.out Nat.prime_two).2 D.gd.l_odd
    obtain ⟨u, hu⟩ := hu
    obtain ⟨s, hs, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B hB u
    refine ⟨s, hs, fun n hn => ?_⟩
    have e2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = ((2 : ℚ) : Qbar l) := by
      show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) (cycZ ℚ Ω l s : ℤ_[l]) = _
      rw [e, hu, map_natCast]
      simp
    have e3 := congrArg Units.val hn
    rw [Units.val_zpow_eq_zpow_val, e2, Units.val_one, ← Rat.cast_zpow] at e3
    have e4 : (2 : ℚ) ^ n = 1 := by exact_mod_cast e3
    exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 e4
  obtain ⟨s₀, hs₀, hn⟩ := hinertia
  have hID : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs
  have flagOfConjugate {Γ k : Type} [Group Γ] [Field k] (I : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ)
      (X : Γ → Matrix (Fin 3) (Fin 3) k) (M : GL (Fin 3) k)
      (hW : ∀ s ∈ I, (W s).val = corner (X s)) (hb : ∀ s ∈ I, ∀ a b, Odd (wt a b) → X s a b = 0) (h1 : ∀ s ∈ I, X s 1 1 = 1)
      (hd : ∀ s ∈ I, (W s).val.det = 1)
      (h0 : ∀ s ∈ I, (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X s * (M : Matrix (Fin 3) (Fin 3) k)) 0 0 = Ψ s)
      (h : ∀ s ∈ I, ∀ i j, wt i j < 0 →
        (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X s * (M : Matrix (Fin 3) (Fin 3) k)) i j = 0)
      (hs : ∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) :
      Af.IsFlagOn W I ![Ψ.comp I.subtype, Ψ⁻¹.comp I.subtype] := by
    have eigenvector {k : Type} [Field k] (M : GL (Fin 3) k) (X : Matrix (Fin 3) (Fin 3) k) (a : k)
        (h0 : (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) 0 0 = a)
        (h : ∀ i j, wt i j < 0 →
          (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) i j = 0) :
        X *ᵥ ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) = a • ((M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1) := by
      have e : (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * X * (M : Matrix (Fin 3) (Fin 3) k)) *ᵥ Pi.single 0 1 =
          a • Pi.single 0 1 := by
        rw [Matrix.mulVec_single_one]
        funext i
        fin_cases i
        · simpa using h0
        · simpa using h 1 0 (by decide)
        · simpa using h 2 0 (by decide)
      rw [← Matrix.mulVec_smul, ← e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.mul_inv, Matrix.one_mul]
    obtain ⟨t, ht, ht₂⟩ := hs
    set v : Fin 3 → k := (M : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ I, X s *ᵥ v = (Ψ s : k) • v := fun s hs => eigenvector M _ _ (h0 s hs) (h s hs)
    have hv1 : v 1 = 0 := by
      have := congrFun (hev t ht) 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hb t ht 1 0 (by decide), hb t ht 1 2 (by decide),
        h1 t ht, zero_mul, zero_add, add_zero, Pi.smul_apply, smul_eq_mul] at this
      by_contra hne
      exact ht₂ (by rw [← mul_right_cancel₀ hne this, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup I I W Ψ ![v 0, v 2]
      (fun d hd s hs => mul_mem (mul_mem (inv_mem hd) hs) hd)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        rw [hW s hs]
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hv1, corner] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hv1, corner] using a2)
      hd ⟨t, ht, ht₂⟩
    have e : κ = ![Ψ.comp I.subtype, Ψ⁻¹.comp I.subtype] := by
      funext i
      fin_cases i
      · exact MonoidHom.ext fun s => (hκ s s.2).1
      · exact MonoidHom.ext fun s => (hκ s s.2).2
    exact e ▸ hflag
  let hMapped := GeneralLinearGroup.map (A.val : A →+* PadicAlgCl l) h
  have hconj (g : G ℚ Ω) (hg : (r g).right = 1) (a b : Fin 3) :
      ((hMapped⁻¹).val * (r g).mat.map A.val * hMapped.val) a b = A.val ((conjBy h⁻¹ r g).mat a b) := by
    have hmat : (conjBy h⁻¹ r g).mat = (h⁻¹).val * (r g).mat * h.val := by
      simp [conjBy, GG.mat, hg]
    rw [hmat]
    change _ = (((h⁻¹).val * (r g).mat * h.val).map (A.val : A →+* PadicAlgCl l)) a b
    rw [Matrix.map_mul, Matrix.map_mul]
    dsimp only [hMapped]
    rw [← map_inv]
    rfl
  have hf := flagOfConjugate (D.η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker ⊓ Ine (F := ℚ) B) W (cycBar ℚ Ω l ^ (e : ℤ))
    (fun g => (UnitaryThreeInertia.push A.val r g).mat) hMapped
    (fun s hs => hW s hs.1.1) (fun s hs => hII.1 s hs.1.1) (fun s hs => congrArg Subtype.val (h11 s hs.1.1))
    (fun s hs => hdet s hs.1.1) (fun s hs => ?_) (fun s hs i j hij => ?_) ?_
  · convert hf using 1
    funext i
    fin_cases i
    · rfl
    · simp
  · refine (hconj s ((hr.red.mult _).trans hs.1.1) 0 0).trans ?_
    have := hT.ine ⟨s, hID s hs.2⟩ hs.2 hs.1.1 0
    refine (congrArg A.val this).trans ?_
    rw [MonoidHom.zpow_apply, ← hΨ s hs.1.2]
    simp [UnitaryThreeInertia.psi, wt1]
    rfl
  · refine (hconj s ((hr.red.mult _).trans hs.1.1) i j).trans ?_
    exact (congrArg A.val (hT.tri ⟨s, hID s hs.2⟩ hs.1.1 i j hij)).trans (map_zero _)
  · refine ⟨s₀ ^ (2 * Nat.card (ZMod N)ˣ), ⟨⟨?_, ?_⟩, pow_mem hs₀ _⟩, fun h0 => ?_⟩
    · show D.η _ = 1
      rw [map_pow, pow_mul, Int.units_sq, one_pow]
    · show ψ.toUnitHom (Chr.cls ℚ Ω N _) = 1
      rw [map_pow, pow_mul', pow_card_eq_one', one_pow, map_one]
    · have := hn (((2 * Nat.card (ZMod N)ˣ : ℕ) : ℤ) * e * 2) (Units.ext (by
        rw [_root_.zpow_mul, _root_.zpow_mul, zpow_two, ← sq, Units.val_pow_eq_pow_val, _root_.zpow_natCast _ (2 * _), ← map_pow]
        exact h0))
      have h3 : 0 < 2 * Nat.card (ZMod N)ˣ * e * 2 := by
        have := D.gd.e_pos
        have := Nat.card_pos (α := (ZMod N)ˣ)
        positivity
      exact h3.ne' (by exact_mod_cast this)
end
