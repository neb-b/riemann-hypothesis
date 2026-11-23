module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TClParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdOrdJac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.CuspUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2OrdPt
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open TensorProduct in
private theorem op_eig {A K M W ι : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module K W] (Y : Submodule A M) [Module.Free A Y] [Module.Finite A Y]
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y, sp (op i f) = opC i (sp f))
    (z : heckeAlg Y op →+* K) (hz : z.comp (algebraMap A _) = χ) :
    ∃ F ∈ Submodule.span K (sp '' Y), F ≠ 0 ∧ ∀ i, opC i F = z (heckeGen Y op i) • F := by
  letI : Algebra A K := χ.toAlgebra
  letI : Module A W := Module.compHom W χ
  haveI : IsScalarTower A K W := ⟨fun a k w => mul_smul (χ a) k w⟩
  let s : Y →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hadd _ f.2 _ g.2
      map_smul' := fun b f => hsmul _ f.2 b }
  have hs : Function.Injective (s.liftBaseChange K) := by
    let b := Module.Free.chooseBasis A Y
    have h1 : s.liftBaseChange K = Finsupp.linearCombination K (fun i => sp (b i)) ∘ₗ (b.baseChange K).repr.toLinearMap :=
      (b.baseChange K).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.linearCombination_single,
          Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [h1, LinearMap.coe_comp]
    exact Function.Injective.comp (hind _ b) (b.baseChange K).repr.injective
  obtain ⟨v, hv, hv'⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig (M := Y)
    ({ z with commutes' := fun b => RingHom.congr_fun hz b } : heckeAlg Y op →ₐ[A] K)
  refine ⟨s.liftBaseChange K v, ?_, fun h => hv (hs (h.trans (map_zero _).symm)), fun i => ?_⟩
  · have h : s.liftBaseChange K v ∈ LinearMap.range (s.liftBaseChange K) := ⟨v, rfl⟩
    rw [LinearMap.range_liftBaseChange] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨f, rfl⟩
    exact ⟨f, f.2, rfl⟩
  · have h1 : opC i ∘ₗ s.liftBaseChange K =
        s.liftBaseChange K ∘ₗ (Algebra.lsmul A A Y (heckeGen Y op i)).baseChange K := by
      ext y
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
      exact (hop i _ y.2).symm
    have h2 := LinearMap.congr_fun h1 v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv', map_smul] at h2
    exact h2
theorem UpperTheory.V.Hi.levelUR2OrdPt_alt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P → ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted → ∀ (K : H.Lev) [Fact (CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A))] (z : heckeAlg (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) →+* Qbar l), z.comp (algebraMap A _) = x.toRingHom → ∃ Y : H.PartAltAlt ι lam ξ, ∀ (w : H.Wp) (k : Fin n), Y.a w (k + 1) = ι (z (heckeGen _ (H.op A) (.inl (w, k)))) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam K _ z hz
  obtain ⟨-, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨F, hF, hF0, h⟩ := op_eig (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) (ι.toRingHom.comp x.toRingHom) sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) (ι.toRingHom.comp z)
    (by rw [RingHom.comp_assoc, hz])
  rw [hsp.span K c0 le_rfl, (_root_.UpperTheory.V.Hi.clParts_alt L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2] at hF
  obtain ⟨Y, hY⟩ := levelUR2EigPart ℂ _ (H.Wp × Fin n) {Y : H.PartAltAlt ι lam ξ // P lam Y.r}
    (fun i => H.opC ι lam d (.inl i)) (fun Y => Y.1.Y) (fun Y i => Y.1.a i.1 (i.2 + 1))
    (fun Y i G hG => Y.1.sph i.1 _ G hG) F (SetLike.le_def.1 (iSup_mono fun _ => inf_le_left) hF) hF0
    (fun i => ι (z (heckeGen _ (H.op A) (.inl i)))) (fun i => h (.inl i))
  exact ⟨Y.1, fun w k => congrFun hY (w, k)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdFlagJ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp
private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp
private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]
theorem UpperTheory.V.Z.Ord.flagJ_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagJ := by
  intro H l _ L Ω _ _ _ _ _ _ s n V c r B Λ J hJ x h ρ hJx hA hx hirr v
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · exact absurd (Subsingleton.elim _ _) hirr.1
    · exact h0
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Ws.Eb.Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => by
    rcases hirr.2.2 N le_top fun g v hv => hN g v hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := descend x.D V.pr hs ρ hn hF hx
  obtain ⟨hO, -⟩ := Ws.Eb.relKill B x ρ₀ hfull hD
  obtain ⟨g₀, hg₀⟩ := _root_.UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy H s h v (x.psi v) hA.1 (hA.2 v)
  refine flag_of_rel _ (x.psi v) (hO v) (fun t => ?_) g₀ hg₀
  let xb : B.B ⧸ J →+* Qbar l := Ideal.Quotient.lift J (x : B.B →+* Qbar l) fun a ha => hJx ha
  have e0 : xb.comp (Ideal.Quotient.mk J) = (x : B.B →+* Qbar l) := RingHom.ext fun a => rfl
  have e1 : (B.DD J).map xb = W.GDet.ofRep (W.mat ρ₀) := by
    have h1 : (B.DD J).map xb = B.u.D.map (xb.comp (Ideal.Quotient.mk J)) := (CA.d_gmap B.u.D).2.1 _ _
    rw [h1, e0]
    exact hD
  have e2 := (AlgebraTools.Det.mapApi (B.DD J) xb).1 (MonoidAlgebra.single (V.frame.φ v t) 1)
  rw [MonoidAlgebra.mapRingHom_single, map_one, e1, (AlgebraTools.Det.repApi _).2.1] at e2
  refine e2.trans ((congrArg (Polynomial.map xb) (hJ.O1 v t)).trans ?_)
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdOrdScal
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem char_at {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {F : M} (hne : F ≠ 0) (h : ∀ t, ∃ a : ℂ, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t)
        rw [map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩
private theorem uOp_at {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  intro F hF
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]
private theorem Uc_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))
private theorem local_exp (hJ : OrdJac) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    {F : M} (hFY : F ∈ Y) (hF0 : F ≠ 0) (e : ℕ) (f : Fin n → Uo k → ℂ)
    (hN : F ∈ fixd ρ (glIwa k n).N) (hNm : F ∈ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (a : ℕ → ℂ)
    (ha : ∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp ρ (al k n (j + 1)) F = a (j + 1) • F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient σ.ρ (PS ω) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧ ∀ j : Fin n, psEig ω (j + 1) = a (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  obtain ⟨p, hp, hp0⟩ := isoSep hσ hFY hF0
  have hpe : p F ∈ (glIwa k n).eig σ.ρ e φ :=
    ⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu],
      fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩
  obtain ⟨ω, h1, h2, h3, h4⟩ := hJ k n σ.V σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j =>
      ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans
        ((congrArg p (ha j).2).trans (map_smul p _ _))⟩
  exact ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩
theorem UpperTheory.V.Z.Ord.ordinary_scalar_of_literal_automorphy_n : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.OrdScalAlt := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb
  classical
  have hN : F ∈ fixd (H.atV d v) (glIwa _ n).N := fun u hu =>
    hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun u hu =>
    hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun i y => by
    have := hF.2.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun j =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·)
      (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)
  have hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0 := fun j h0 => by
    have := (hb j).2
    rw [hop j, h0, inv_zero, zero_smul] at this
    exact smul_ne_zero (hb j).1 hF0 this.symm
  let a : ℕ → ℂ := fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)
  have ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j := fun j => by
    have h : (j : ℕ) + 1 - 1 < n := by simpa using j.2
    simp only [a, dif_pos h]
    congr 2
  obtain ⟨ω, h1, h2, h3, h4⟩ := local_exp (_root_.UpperTheory.V.Z.Ord.ordinary_jacquet_of_literal_automorphy_n hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT
    (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j =>
      ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, by
        have h := (hop j).symm.trans (hb j).2
        rw [inv_smul_eq_iff₀ (hl j), smul_smul] at h
        rw [ha j]
        exact h⟩
  exact ⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRSol
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol
namespace UpperTheory.V.Z.Bc
theorem exDownC_sv_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : CycC) : ExDownC := by
  have hA0 := _root_.UpperTheory.V.Af.algOfCyc_s H
  have hTo := UpperTheory.cyclotomicCharacter_plusPart hA0 UpperTheory.cyclotomic_char_conj_invariant
  have hDual := UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder UpperTheory.frobeniusDuality_complexConj UpperTheory.complexConj_place_under_eq
  have hNorm := _root_.UpperTheory.norm_character_of_printed_char_frobenius H.toClassicalTheorems UpperTheory.galois_character_frobenius_compatibility
  have hFin := UpperTheory.finiteCharacter_of_algebraic_cyclotomic hA0
  have hExt := UpperTheory.character_extends_to_galois_group
  have hEig := UpperTheory.hecke_eigenvalue_basic_properties
  have hSign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l _ ι n hn r π sat' inf' hpol hreg hc' hbc hatt
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := hTo K Ω l ι n r hpol
  have huniq : ∀ w B B', sat' w B → sat' w B' → B = B' := by
    rcases hc' with ⟨_, Q, rfl, -⟩ | ⟨_, Q, rfl, -⟩
    · exact fun _ _ _ h h' => h.unique h'
    · exact fun _ _ _ h h' => TR.CuspSub.HasSat.unique h h'
  have hbc' := hDual K M Ω l ι n r π sat' huniq hbc hatt μ χ c P hμ hc hP
  obtain ⟨η, hη, hev⟩ := (cyc K M hp inferInstance n hn).2.2 _ _ sat' inf'
    (Or.inl ⟨inferInstance, π, rfl, rfl⟩) hc' hbc _ _ (Or.inl ⟨inferInstance, _, rfl, rfl⟩) hbc'
  obtain ⟨δ, hδ, hδe⟩ := hNorm K M Ω l ι η hη
  obtain ⟨δ', hδ', hδc, hδo⟩ := hExt K M Ω l δ hδ
  have hA := (_root_.UpperTheory.V.Af.algOfCyc_s H (maximalRealSubfield K) Ω l ι).2.1
  have h1 : IsAlgChar ι μ := ⟨χ, hμ⟩
  have h2 := hFin.1 _ Ω l ι δ' hδo
  obtain ⟨χ', hχ'⟩ := (hA _ _ h1 (hA _ _ h2 h2).2).1
  have hs' : SameSign (μ * δ'⁻¹) := fun a b ha hb => by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, hδc a ha, hδc b hb, hs a b ha hb]
  have hd : GlobalTheory.ContraPair.DualIsConjBy π (compNorm K χ') := by
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk K n hn π _ ?_
    have h3 := (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hev
    filter_upwards [Bc.normGal K Ω l ι χ μ hμ, Bc.normGal K Ω l ι χ' _ hχ', hev, h3, hδe] with w ⟨hu, he⟩ ⟨hu', he'⟩
      ⟨_, B, hB, hB₁⟩ ⟨_, B', hB', _⟩ hw
    refine ⟨hu', B, B', hB, hB', ?_⟩
    have e1 : (μ * δ'⁻¹).comp (res (maximalRealSubfield K) Ω K) = μ.comp (res (maximalRealSubfield K) Ω K) * δ⁻¹ := by
      rw [← hδ']
      rfl
    rw [e1] at he'
    have e2 := (hEig K Ω l ι w).2.1 _ _ _ he' ((hEig K Ω l ι w).1 _ _ _ _ he hw)
    have e3 := hB₁.unique (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) w _ hu (UpperTheory.theta_satake_parameters_inverse K n π w B' hB'))
    have e4 := congrArg (Multiset.map (· * ((compNorm K χ).val w)⁻¹)) e3
    simp only [Multiset.map_map, Function.comp_def, mul_inv_cancel_right] at e4
    rw [← e4, e2]
    refine Multiset.map_congr rfl fun a _ => ?_
    rw [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨_, R, _, _, _, hR, hatt', -⟩ := _root_.UpperTheory.Gal.SV.exCS_of_prints H.toClassicalTheorems K Ω l ι n hn π χ' hreg (hSign _ Ω l ι χ' _ hχ' hs') hd
  exact ⟨R, hR.cont, hatt'⟩
end UpperTheory.V.Z.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinPairs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AAcross2Alt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → RowT → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ r : G ℚ Ω →* GL (Fin n) (Qbar l), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) →
    Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsAlgChar ι θ ∧ DualTw r θ) → IneAb r → Flagged r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) →
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → WitAQ ι r
variable {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
end UpperTheory.V.Z.Win
end
end
end

