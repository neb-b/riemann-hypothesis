module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWPtAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
open scoped Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem adjoint_vanishing_gsp4_rigid_point (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) {D : Raw Ω c} (hG : D.Good) {T : Tower D} (hF : T.Fit) (hD : T.Deep) {c' : Coef l}
    {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ι : PadicAlgCl l ≃+* ℂ)
    (r r₁ : G ℚ Ω →* M4 (PadicAlgCl l)) (hconj : IsConj4 r r₁)
    (hres : r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r)
    (hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l))) (hc : Continuous r) (hm : D.Mult r)
    (hi : Irr (r.comp T.L.fixingSubgroup.subtype)) (haut : Af.IsAut ι (r.toHomUnits.comp (resQ T.L)))
    (hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L))) (hf : FreeAt l (r.toHomUnits.comp (resQ T.K))) :
    ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) (Qbar l), ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) ∧ AdZero K.V ρ := by
  obtain ⟨⟨B, -⟩, hB⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hB B
  obtain ⟨u, hu⟩ := hconj
  have hcj : ∀ g, K.rhoQ 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r g = u * K.rhoQ 0 (r.comp (resQ T.F)) g * u⁻¹ := fun g => by
    apply Units.ext
    rw [← hres, Units.val_mul, Units.val_mul, K.rho_val, K.rho_val, MonoidHom.comp_apply, MonoidHom.comp_apply, hu,
      Matrix.mul_smul, Matrix.smul_mul]
  have hrep₁ : (Link.pt φ y).IsRep (K.rhoQ 0 _) := auRep D T c' h K X B 0 φ hφ y _ fun _ => rfl
  have hrep : (Link.pt φ y).IsRep (K.rhoQ 0 (r.comp (resQ T.F))) := by
    refine Eq.trans hrep₁ ((AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ u fun g => ?_).symm
    exact congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hcj g)).symm
  have hcρ := Pt.rho_cont K 0 (r := r.comp (resQ T.F)) (hc.comp (Af.continuous_restrictScalarsHom ℚ T.F Ω))
  have hirr : Af.IsIrr (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).2 (K.twc 0)
  have hfull : Eb.Full (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (AlgebraTools.Det.irrIffSpan (W.mat _)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  obtain ⟨hs, hq, -⟩ := phiKer K.V
  let τ := K.rhoQ 0 (r.comp (resQ T.F))
  have hchi (g : G T.L Ω) :
      (Link.pt φ y).D.chi (MonoidAlgebra.single (K.V.pr g) 1) =
        (W.GDet.ofRep (W.mat τ)).chi (MonoidAlgebra.single g 1) := by
    rw [← hrep]
    change (Link.pt φ y).D.D (PadicAlgCl l)[X] _ =
      (Link.pt φ y).D.D (PadicAlgCl l)[X] (MonoidAlgebra.mapDomainRingHom (PadicAlgCl l)[X] K.V.pr _)
    congr 1
    rw [map_sub]
    simp
    let pg : K.V.frame.G₀ := K.V.pr g
    change MonoidAlgebra.single (1 : K.V.frame.G₀) Polynomial.X -
        MonoidAlgebra.mapRingHom K.V.frame.G₀ C (MonoidAlgebra.single pg (1 : Qbar l)) =
      MonoidAlgebra.single (1 : K.V.frame.G₀) Polynomial.X - MonoidAlgebra.single pg 1
    rw [MonoidAlgebra.mapRingHom_single, map_one]
    exact Eq.refl _
  have hker : K.V.pr.ker ≤ τ.ker := fun g hg => by
    have htrace := (AlgebraTools.Det.repApi (W.mat τ)).2.2.1 (by decide)
    have hzero := (Eb.trPlus τ hfull).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun a => by
      have e : (W.GDet.ofRep (W.mat τ)).tr (MonoidAlgebra.single (a * g) 1) =
          (W.GDet.ofRep (W.mat τ)).tr (MonoidAlgebra.single a 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [htrace, htrace] at e
      rw [htrace, mul_sub, map_sub, Matrix.trace_sub, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at hzero
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using hzero
  let ρ := K.V.pr.liftOfSurjective hs ⟨τ, hker⟩
  have hρ : ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) :=
    MonoidHom.liftOfRightInverse_comp K.V.pr (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨τ, hker⟩
  have hfull' : Eb.Full ρ := by
    refine top_le_iff.1 (le_trans (le_of_eq hfull.symm) (Submodule.span_mono ?_))
    rintro _ ⟨g, rfl⟩
    exact ⟨K.V.pr g, congrArg Units.val (DFunLike.congr_fun hρ g)⟩
  refine ⟨ρ, hρ, ?_⟩
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4]
    omega
  obtain ⟨m, hmm, k, hk, hmk⟩ := Pt.ptWts K X B 0 φ hφ y _ (fun i => by simp) hw
  obtain ⟨π, hreg, hatt⟩ := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.L Ω l ι 4 _).2.1.1 haut
  have haut' : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ 0 (r.comp (resQ T.F))) := by
    have e : Af.tw ((r.comp (resQ T.F)).comp (resLe T.F_le)).toHomUnits 1 = r.toHomUnits.comp (resQ T.L) := by
      ext g : 2
      rw [Af.tw_val, MonoidHom.one_apply, Units.val_one, one_smul]
      rfl
    refine _root_.UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four hU.pr K 0 ι _ (fun g => hm _) 1 π 0 1 continuous_const one_pos (by simp) (fun A _ s _ => by simp) hreg ?_ ?_ <;>
      rwa [e]
  have hunr := Pt.ptUnr K 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl : ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ 0 (r.comp (resQ T.F))).comp (Dec (F := T.L) (K.s.A v)).subtype)
      ((Link.pt φ y).psi v) := fun v => by
    obtain ⟨a, ha⟩ := Pt.ptFlag K X B 0 φ hφ y v
    refine ⟨a * u, fun s => ?_⟩
    have h1 := ha s
    rw [MonoidHom.comp_apply, hcj] at h1
    simpa only [mul_inv_rev, mul_assoc, MonoidHom.comp_apply] using h1
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι (Link.pt φ y) ρ := by
    refine ⟨hq.continuous_iff.2 ?_, hρ ▸ hrep, ?_, hρ ▸ haut', ?_, fun v => ?_⟩
    · have e : (ρ : _ → _) ∘ K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) := congrArg DFunLike.coe hρ
      exact e ▸ hcρ
    · exact auArith hU.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y _ (fun _ => rfl) (Pt.psi_cont _) _ hanti hw
    · rintro _ ⟨g, hg, rfl⟩
      have h1 := hunr g hg
      rw [hcj, mul_inv_eq_one, mul_eq_left] at h1
      exact (DFunLike.congr_fun hρ g).trans h1
    · have h1 := hfl v
      rw [← hρ] at h1
      exact h1
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ)).2 hfull' N fun g v hv => hN g trivial v hv
  have hfree : Free K.V.frame fun v => (Link.pt φ y).psi v := fun v : W.Vl l T.L => by
    have : IsGalois ℚ Ω := {}
    obtain ⟨g, hg, hc, α, hα, hcp⟩ := hf (K.s.A v) (by simpa using (K.s.hA v _).2 v.2)
    have hi : T.L.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index Ω T.L]
      exact Module.finrank_pos.ne'
    obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi (resQ T.K g)
    let σ : G T.L Ω := IntermediateField.fixingSubgroupEquiv T.L ⟨_, hmem⟩
    have hσ : resQ T.L σ = resQ T.K (g ^ m) := by rw [map_pow]; rfl
    have hdec : σ ∈ Dec (F := T.L) (K.s.A v) := by
      have hpow : resQ T.K (g ^ m) ∈ Dec (F := ℚ) (K.s.A v) :=
        (pow_mem hg m : g ^ m ∈ Dec (F := T.K) (K.s.A v))
      rw [← hσ] at hpow
      exact hpow
    let s : Dec (F := T.L) (K.s.A v) := ⟨σ, hdec⟩
    refine ⟨s, ?_, ?_⟩
    · have hcyc : cycZ ℚ Ω l (resQ T.K (g ^ m)) = 1 := by
        show cycZ T.K Ω l (g ^ m) = 1
        rw [map_pow, hc, one_pow]
      rw [← hσ] at hcyc
      exact (DFunLike.congr_fun K.V.hε _).trans hcyc
    · let M := W.mat (r.toHomUnits.comp (resQ T.K)) g
      let κ := K.twc 0 σ
      let ψ := fun i => (Link.pt φ y).psi v i s
      have hcp' : ((κ : Qbar l) • M ^ m).charpoly = ∏ i, (Polynomial.X - C (ψ i : Qbar l)) := by
        obtain ⟨a, ha⟩ := hfl v
        have htri : ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)).IsUpperTriangular :=
          fun i j hij => (ha s).1 i j hij
        have hconjChar : ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)).charpoly =
            (τ σ : M4 (Qbar l)).charpoly := by
          simpa only [Units.val_mul, Matrix.coe_units_inv] using
            Matrix.charpoly_units_conj a (τ σ : M4 (Qbar l))
        have hmat : (τ σ : M4 (Qbar l)) = (κ : Qbar l) • M ^ m := by
          rw [show τ = K.rhoQ 0 (r.comp (resQ T.F)) from rfl, K.rho_val]
          change (κ : Qbar l) • r (resQ T.L σ) = (κ : Qbar l) • (r (resQ T.K g)) ^ m
          rw [hσ, map_pow, map_pow]
        rw [← hmat, ← hconjChar, Matrix.charpoly_of_isUpperTriangular _ htri]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show ((a * τ σ * a⁻¹ : GL (Fin 4) (Qbar l)) : M4 (Qbar l)) i i = ψ i from (ha s).2 i]
      have hmatch (i : Fin 4) : ∃ j, ψ j = κ * α i ^ m := by
        have hdet : (Matrix.scalar (Fin 4) (α i : Qbar l) - M).det = 0 := by
          rw [← Matrix.eval_charpoly, hcp, eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
        obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
        have heig : M *ᵥ x = (α i : Qbar l) • x := by
          rw [Matrix.sub_mulVec, sub_eq_zero] at hMx
          rw [← hMx]
          ext j
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        have hpow (k : ℕ) : M ^ k *ᵥ x = (α i : Qbar l) ^ k • x := by
          induction k with
          | zero => simp
          | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
        have hdet' : (Matrix.scalar (Fin 4) ((κ : Qbar l) * (α i : Qbar l) ^ m) -
            (κ : Qbar l) • M ^ m).det = 0 := by
          refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, ?_⟩
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hpow, smul_smul, sub_eq_zero]
          ext j
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        rw [← Matrix.eval_charpoly, hcp', eval_prod] at hdet'
        obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 hdet'
        refine ⟨j, Units.ext ?_⟩
        simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
        simpa using hj.symm
      choose p hp using hmatch
      have hinj : Function.Injective p := fun i j hij => by
        by_contra hne
        exact hα i j hne m hm (mul_left_cancel ((hp i).symm.trans (hij ▸ hp j)))
      have hsurj := Finite.surjective_of_injective hinj
      intro i j hij k hk e
      obtain ⟨i, rfl⟩ := hsurj i
      obtain ⟨j, rfl⟩ := hsurj j
      change ψ (p i) ^ k = ψ (p j) ^ k at e
      rw [hp, hp, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at e
      exact hα i j (fun h => hij (congrArg p h)) _ (mul_pos hm hk) (mul_left_cancel e)
  exact hAd l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by omega) le_rfl K.r K.v0 B ι _ ρ
    (_root_.UpperTheory.V.Th.nice0four_alt ι _ ρ hapt hirr₀ hfree (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K))
    (by
      intro v
      refine ⟨m v, k, ?_, hk, fun i j g hg => ?_⟩
      · intro i j hij
        have h1 := hmm v i j
        have h2 := hanti hij
        simp only at h1 h2
        omega
      · let ψ := (Link.pt φ y).psi v
        change (ψ i g / ψ j g * cycBar T.L Ω l g ^ (m v j - m v i)) ^ k = 1
        have e : ψ i g / ψ j g * cycBar T.L Ω l g ^ (m v j - m v i) =
            (ψ i g * cycBar T.L Ω l g ^ (-m v i)) / (ψ j g * cycBar T.L Ω l g ^ (-m v j)) := by
          rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
          congr 2
          ring
        rw [e, div_pow, hmk v i g hg, hmk v j g hg, div_one])
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
