module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.EndOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0065
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0060
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocSubD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlAllOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpToTW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocDataT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoOfDet
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
set_option synthInstance.maxHeartbeats 200000
section SlopeTestRemainingChoices
variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩
private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩
private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]
private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
private theorem push_comp {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (χ : Γ →* Aˣ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : W.pushCh y (W.pushCh f χ) = W.pushCh x χ := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
end SlopeTestRemainingChoices
set_option maxHeartbeats 1000000 in
private theorem absPt (hC : _root_.UpperTheory.V.Z.Ord.CoreOrdAlt) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
    (hθ : H.IsWt θ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop}
    (hP : _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P) (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)
    (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hm : H.IsMap θ a K D₀ ψ₀ f) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n)
    (hl : lam ∈ H.admitted) (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ), P lam d ξ Y ∧ D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat Y.r) ∧
      ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
        ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh (x : R →+* Qbar l) (ψ₀ v i)) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  have har' : H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam := by rw [e1]; exact har
  unfold HSet.IsMap at hm
  obtain ⟨d, ξ, Y, hY, hD, hω⟩ := hC L Ω l n c H hA A θ hθ ι P hP a K _ _ hm lam hl y har'
  refine ⟨d, ξ, Y, hY, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD, fun v => ?_⟩
  obtain ⟨ω, h1, h2⟩ := hω v
  refine ⟨ω, h1, fun i => ?_⟩
  have := h2 i
  rwa [push_comp _ f.toRingHom y.toRingHom x hy] at this
set_option maxHeartbeats 1000000 in
private theorem core (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q R.τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q R.τ₀).PartAltAlt ι lam ξ),
      (Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q R.τ₀).Sl v) (Y.σl v)) ∧
      x.IsRep (Y.r.comp V.pr) ∧
      ∀ v : Vl l L, ∃ ω : Fin n → (((hset Q R.τ₀).Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
        ∀ i, OrdChar ι ((hset Q R.τ₀).art v) (ω i) (htW lam i) (x.psi v i) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  obtain ⟨d, ξ, Y, hY, hD, hω⟩ := absPt (_root_.UpperTheory.V.Z.Ord.core_ordinary_of_literal_automorphy_n H.litN) (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀) R.θ R.isWt ι
    (_root_.UpperTheory.Gal.projectedFormsSystemPart.autUO_of_printsH H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) R.a K B.u.D B.u.ψ (Λ.toPair B.u) f hmap hsurj hlam x hx lam (Set.mem_univ _) har
  refine ⟨lam, d, ξ, Y, hY, ?_, hω⟩
  replace hD : x.D = W.GDet.ofRep (W.mat Y.r) := hD
  change x.D.comap V.pr = _
  rw [hD]
  exact (AlgebraTools.Det.repApi (W.mat Y.r)).2.2.2.2.2.2.1 V.pr
set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Ord.endOrd_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Z.Ord.EndOrdAlt := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K J hJ x h ρ hx ha hρ hi
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨lam, d, ξ, Y, hP, hr, hω⟩ := core H hn hJ x h hx ha
  have e : Af.RepIso (Y.r.comp V.pr) ρ := iso_of_det (ss_of_irr hi) (ss_comp hpr Y.ss) (hρ.symm.trans hr)
  obtain ⟨π, h1, h2, h3, h4⟩ := hP (irr_iso e.symm' hi)
  refine ⟨π, h1, h2, ⟨ss_of_irr hi, h3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩, fun v => ?_⟩
  obtain ⟨ω, hs, ho⟩ := hω v
  refine ⟨(hset Q R.τ₀).art v, (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀).art_spec v, fun j => htW lam j, ω, fun τ i j hij => ?_, ho,
    fun σ hσ => ?_⟩
  · have h1 := (lam τ).anti (Fin.rev_le_rev.2 hij.le)
    have h2 : (i : ℕ) < j := hij
    simp only [htW, lowW]
    omega
  · obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π _ σ (Y.σl v) hσ (h4 v)
    exact (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective).trans hs
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemLevelOfLocalDepth
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem compD :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w → ∀ W : Sig.Lev (Kw w),
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ (g * x) = φ g) →
        ∀ ψ : Fin n → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w W ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw W φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, _root_.UpperTheory.V.Z.Sym.W.local_sub_d_statement H _ n W ψ hψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap W _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap W ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap W ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _
private theorem mem_level_of_local_depth {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S₀ S : Finset (Plc L)} {c : ℕ}
    (hS : Places ((S₀ : Set (Plc L)) ∪ S)) (hd : Disjoint S₀ S) {w : Plc L} (hw : w ∈ S₀) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (deep c w).J n) : x ∈ lev (lev (Kall L n) S₀ (deep c)) S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (deep c w)).2.2.2.2.2 n).2.2.2 hJ
  have key : ∀ w' ∈ (S₀ : Set (Plc L)) ∪ S, w' ≠ w → cLoc w' x = 1 := fun w' hw' e => by
    have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' (Or.inl hw) h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    exact MonoidHom.mem_ker.1 (this w' rfl)
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨⟨hk, fun w' hw' => ?_⟩, fun w' hw' => ?_⟩
  · by_cases e : w' = w
    · subst e; exact hJ
    · rw [Subgroup.mem_comap, key w' (Or.inl hw') e]
      exact one_mem _
  · rw [Subgroup.mem_comap, key w' (Or.inr hw') fun e => Finset.disjoint_left.1 hd hw (e ▸ hw')]
    exact one_mem _
private theorem outW :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ (S₀ : Finset (Plc L)) (c : ℕ) (U : Subgroup (UA L n)), U = lev (Kall L n) S₀ (deep c) → IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
          ∀ S : Finset (Plc L), Places ((S₀ : Set (Plc L)) ∪ S) → Disjoint S₀ S → Places (S : Set (Plc L)) → (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
          ∀ (ψ : ∀ w : Plc L, Fin n → (Kw w)ˣ →* ℂˣ) (φ : UA L n → V), φ ≠ 0 → IsAF R (lev U S iw) φ →
          (∀ w ∈ S, (∀ i, ∀ u ∈ UpperTheory.V.Hi.Uo (Kw w), ψ w i u = 1) ∧ (∀ i i', i ≠ i' → ψ w i ≠ ψ w i' ∧ ψ w i ≠ ψ w i' * absPow (Kw w) 1) ∧
            EigT φ w (iw w) (ψ w)) → (∀ w ∈ S₀, (∀ i, IsSmoothChar (ψ w i)) ∧ EigT φ w (deep c w) (ψ w)) →
          ∃ σ ∈ A, (∀ w ∈ S₀, CompSub σ w (ψ w)) ∧ ∀ w ∈ S, CompSub σ w (ψ w) := by
  intro H L _ _ _ unr n hn V _ _ _ R hR S₀ c U eU hU
  obtain ⟨A, hA, hA', h⟩ := UpperTheory.V.Z.Sym.U.finFamU L n V R hR U hU
  refine ⟨A, hA, hA', fun S hP hd hS hK ψ φ h0 hφ hψ hψ0 => ?_⟩
  obtain ⟨π, φ₁, hπ, h1, hφ₁, hc, he⟩ := proj L n V R hR _ ((cof L n).2.2.1 U hU S iw) φ h0 hφ
  have hcs : ∀ w ∈ S, CompSub π w (ψ w) := fun w hw =>
    _root_.UpperTheory.V.Z.Sym.Al.comp_sub_of_eigen_vector_fixed_by_j H L unr n hn V π hπ w (hS.split w hw) φ₁ h1 hc (fun x hx hJ => hφ₁.level x (mem_lev hS hK hw hx hJ)) (ψ w)
      (fun i => (unrSmooth _).1 _ ((hψ w hw).1 i)) fun d hd => he _ _ _ _ ((hψ w hw).2.2 d hd)
  have hc0 : ∀ w ∈ S₀, CompSub π w (ψ w) := fun w hw =>
    compD H L unr n hn V π hπ w (hP.split w (Or.inl hw)) (deep c w) φ₁ h1 hc
      (fun x hx hJ => hφ₁.level x (eU ▸ mem_level_of_local_depth hP hd hw hx hJ)) (ψ w) (hψ0 w hw).1 fun d hd => he _ _ _ _ ((hψ0 w hw).2 d hd)
  obtain ⟨φ₂, h2, hc2, hφ₂⟩ := raise L n V R π hπ U hU.1 S hS
    (fun w hw => ⟨hK w hw, _root_.UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters H L n π w (ψ w) (hS.split w hw) (hcs w hw) (hψ w hw).1 (hψ w hw).2.1⟩) iw φ₁ h1 hc hφ₁
  obtain ⟨σ, hσ, ht⟩ := h π hπ φ₂ h2 hφ₂ hc2
  refine ⟨σ, hσ, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨a, τ, b, c⟩ := hc0 w hw
    exact ⟨a, τ, ht w τ b, c⟩
  · obtain ⟨a, τ, b, c⟩ := hcs w hw
    exact ⟨a, τ, ht w τ b, c⟩
private theorem smo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ : Fin 2 → kˣ →* ℂˣ}
    (h : ∀ i, IsSmoothChar (ψ i)) : ∀ i, IsSmoothChar ((![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹] : Fin 3 → kˣ →* ℂˣ) i) := by
  have h1 : IsSmoothChar (ψ 0 / ψ 1) := by
    rw [div_eq_mul_inv]
    exact (h 0).mul (h 1).inv
  intro i
  fin_cases i
  · exact h1
  · have := h1.mul h1.inv
    rwa [mul_inv_cancel] at this
  · exact h1.inv
private theorem unram_of {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) (h : ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ lev (Kall L n) S V, RU L n u φ = φ) (w : Plc L)
    (hw : ∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : IsUnramU σ w := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨φ, h1, h2, fun x hx hK => h3 x ?_⟩
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨((factor L n w).2.2.2.2.1 x hx).2 hK, fun w' hw' => ?_⟩
  have := (factor L n w').2.2.1 w (hw w' hw').symm hx
  simp only [away, Subgroup.mem_iInf] at this
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
  exact one_mem _
private theorem pigeon {X I : Type} (A : Set X) (hA : A.Finite) (P : X → I → Prop)
    (h : ∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) : ∃ x ∈ A, ∀ i, P x i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf using fun x : A => hn x.1 x.2
  haveI := hA.fintype
  obtain ⟨x, hx, h1⟩ := h (Finset.univ.image f)
  exact hf ⟨x, hx⟩ (h1 _ (Finset.mem_image_of_mem f (Finset.mem_univ _)))
theorem UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → UpperTheory.V.Z.Sym.W.SpecOutS → UpperTheory.V.Z.Sym.W.AdLiftW := by
  classical
  intro H hS L _ _ _ unr S₀ P hdis hpl htwo π hπ j hj hwt hunr ψ hψ hP
  have mono : ∀ {T : Set (Plc L)}, T ⊆ (S₀ : Set (Plc L)) ∪ P → Places T := fun h =>
    ⟨fun w hw => hpl.split w (h hw), hpl.inj.mono h⟩
  obtain ⟨c₀, hc₀⟩ := hS L unr S₀ (mono Set.subset_union_left) htwo j hj
  have hd : ∀ p : S₀ × Fin 2, ∃ c₁ : ℕ, ∀ c ≥ c₁, ∀ u ∈ UpperTheory.V.Hi.Uc (Kw p.1.1) (c + 1), ψ p.1.1 p.2 u = 1 := fun p =>
    smoothDepth _ _ ((hψ p.1.1 (Or.inl p.1.2)).1 p.2)
  choose c₁ hc₁ using hd
  obtain ⟨c, hc, hc'⟩ : ∃ c, c₀ ≤ c ∧ ∀ p, c₁ p ≤ c :=
    ⟨max c₀ (Finset.univ.sup c₁), le_max_left _ _, fun p => (Finset.le_sup (Finset.mem_univ p)).trans (le_max_right _ _)⟩
  obtain ⟨U₂, hU₂, hm⟩ := hc₀ c hc
  obtain ⟨⟨f3, c3⟩, -⟩ := contE (InfinitePlace L) j
  obtain ⟨-, f2, c2⟩ := contE (InfinitePlace L) (2 * j + 1)
  have hU₃ : IsLevel (lev (Kall L 3) S₀ (deep c)) := (cof L 3).2.2.1 _ (cof L 3).2.1 _ _
  obtain ⟨A₃, hA₃, hA₃', h₃⟩ := outW H L unr 3 (by norm_num) _ _ c3 S₀ c _ rfl hU₃
  obtain ⟨A₂, hA₂, hA₂', h₂⟩ := _root_.UpperTheory.V.Z.Sym.Al.outRep_alt H L unr 2 (by norm_num) _ _ (c2 0) _ hU₂
  let Gd : Plc L → Prop := fun w => locU 2 w ⊓ Kall L 2 ≤ U₂ ∧ locU 3 w ⊓ Kall L 3 ≤ lev (Kall L 3) S₀ (deep c)
  have hG : ∀ᶠ w in Filter.cofinite, Gd w := ((cof L 2).2.2.2 _ hU₂).and ((cof L 3).2.2.2 _ hU₃)
  let Q : Submodule ℂ (UA L 3 → ℂ) ⊕ Submodule ℂ (UA L 2 → ℂ) → Plc L → Prop := fun x w =>
    x.elim (fun σ => CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹])
      fun σ => ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2
  obtain ⟨x, hx, hQ⟩ := pigeon (I := {w // w ∈ P ∧ Gd w}) (Sum.inl '' {σ ∈ A₃ | ∀ w ∈ S₀, CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]} ∪ Sum.inr '' A₂) (((hA₃.subset (Set.sep_subset _ _)).image _).union (hA₂.image _))
    (fun x w => Q x w.1) fun S => by
      let S₁ : Finset (Plc L) := S.image Subtype.val
      have h1 : ∀ w ∈ S₁, w ∈ P ∧ Gd w := fun w hw => by
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hw
        exact y.2
      have hn : ∀ w ∈ S₁, w ∉ S₀ := fun w hw h => Set.disjoint_left.1 hdis h (h1 w hw).1
      have hsub : ((S₀ : Set (Plc L)) ∪ S₁) ⊆ (S₀ : Set (Plc L)) ∪ P := Set.union_subset_union_right _ fun w hw => (h1 w hw).1
      have hp1 : Places (S₁ : Set (Plc L)) := mono fun w hw => Or.inr (h1 w hw).1
      let W : ∀ w : Plc L, Sig.Lev (Kw w) := fun w => if w ∈ S₀ then deep c w else iw w
      have W0 : ∀ w ∈ S₀, W w = deep c w := fun w hw => if_pos hw
      have W1 : ∀ w ∈ S₁, W w = iw w := fun w hw => if_neg (hn w hw)
      obtain ⟨e, φ, h0, hAF, hE⟩ := _root_.UpperTheory.V.Z.Sym.Al.inVec_alt H L π hπ j hwt (S₀ ∪ S₁) (by rw [Finset.coe_union]; exact mono hsub)
        (fun w hw => hunr w fun w' hw' => hw w' (Finset.mem_union_left _ hw')) W ψ fun w hw => by
          rcases Finset.mem_union.1 hw with hw | hw
          · exact ⟨hψ w (Or.inl hw), fun i => by rw [W0 w hw]; exact hc₁ (⟨w, hw⟩, i) c (hc' _)⟩
          · exact ⟨hψ w (Or.inr (h1 w hw).1), fun i => by rw [W1 w hw]; exact (hP w (h1 w hw).1).1 i⟩
      have hle : lev (lev (Kall L 2) S₀ (deep c)) S₁ iw ≤ lev (Kall L 2) (S₀ ∪ S₁) W := by
        intro u hu
        simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf] at hu ⊢
        refine ⟨hu.1.1, fun w hw => ?_⟩
        rcases Finset.mem_union.1 hw with hw | hw
        · rw [W0 w hw]; exact hu.1.2 w hw
        · rw [W1 w hw]; exact hu.2 w hw
      rcases hm S₁ (Finset.disjoint_right.2 hn) (mono hsub) (fun w hw => (h1 w hw).2.1) (fun w => ψ w 0 / ψ w 1) e φ h0
        ⟨hAF.left, hAF.inf, fun u hu => hAF.level u (hle hu)⟩
        (fun w hw => eigTS L _ φ w _ _ (W0 w hw ▸ hE w (Finset.mem_union_left _ hw)))
        (fun w hw => eigTS L _ φ w _ _ (W1 w hw ▸ hE w (Finset.mem_union_right _ hw))) with ⟨φ', a0, a1, a3, a2⟩ | ⟨φ', a0, a1, a2⟩
      · obtain ⟨σ, hσ, hs0, hs⟩ := h₃ S₁ (mono hsub) (Finset.disjoint_right.2 hn) hp1 (fun w hw => (h1 w hw).2.2) (fun w => ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) φ' a0 a1
          (fun w hw => ⟨(regUnl _ _ (hP w (h1 w hw).1).2).1.1, (regUnl _ _ (hP w (h1 w hw).1).2).1.2, a2 w hw⟩)
          fun w hw => ⟨smo (hψ w (Or.inl hw)).1, a3 w hw⟩
        exact ⟨.inl σ, Or.inl ⟨σ, ⟨hσ, hs0⟩, rfl⟩, fun i hi => hs i.1 (Finset.mem_image_of_mem _ hi)⟩
      · obtain ⟨φ'', ψ', b0, b1, b2⟩ := UpperTheory.V.Z.Sym.Al.refine L _ _ U₂ hU₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) _ φ' a0 a1 a2
        obtain ⟨σ, hσ, hs⟩ := h₂ S₁ hp1 (fun w hw => (h1 w hw).2.1) ψ' φ'' b0 b1
          fun w hw => ⟨(b2 w hw).1, (regUnl _ _ (hP w (h1 w hw).1).2).2 _ (b2 w hw).2.1, (b2 w hw).2.2⟩
        exact ⟨.inr σ, Or.inr ⟨σ, hσ, rfl⟩, fun i hi =>
          ⟨ψ' i.1, hs i.1 (Finset.mem_image_of_mem _ hi), (b2 i.1 (Finset.mem_image_of_mem _ hi)).2.1⟩⟩
  rcases hx with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩
  · exact Or.inl ⟨σ, (hA₃' σ hσ.1).1, unram_of _ _ _ (hA₃' σ hσ.1).2, hσ.2, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
  · exact Or.inr ⟨σ, hA₂' σ hσ, hG.mono fun w hw hw' => hQ ⟨w, hw', hw⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewAdmS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.newAdmS_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ)
    (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hirr : IsIrr W)
    (hf : (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ _root_.UpperTheory.V.Z.Win.WitAQ ι W)
    (hlev : Level l M ![(e : ℤ), -(e : ℤ)] W) (hcyc : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    _root_.UpperTheory.GalN.V.AdmRNAlt ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := hf
  exact ⟨hirr, _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (_root_.UpperTheory.GalN.V.newformAut0_alt P (2 * e + 1) (by omega) f l Ω ι W _ hf) fun _ => hw, hlev, ⟨_, hcyc, dual_two W⟩,
    _root_.UpperTheory.V.Z.Win.A4.safeUGap' hlev fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasAutOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Pa.has_automorphy_of_statement : _root_.UpperTheory.V.Pa.HasAutOfAlt := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hS hLev T Q
  obtain ⟨b, hb⟩ := hLev
  choose ut hut using fun (j : Fin T.q) (i : Fin n) =>
    residue_surjective (R := O) (((residOf r).chib i (T.sg j) : (ResidueField O)ˣ) : ResidueField O)
  have key : ∀ N, ∃ A' : TWRing b (T.h N) ut N, Nonempty (TWMaps (T.Nq N) (T.ph N) (T.ta N) A' n.factorial) := by
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => _root_.UpperTheory.V.Z.Win.locDataT_alt hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := _root_.UpperTheory.V.Pa.Lev.opOf_alt hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransport l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact opToTW l _ _ O n _ B.B _ J _ b _ (T.h N) T.q N A2 _ _ _ _ ut h2
  choose A hA using key
  exact ⟨⟨b, ut, hut, A, n.factorial, fun N => (hA N).some⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasOp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Th.has_operator_statement :
    _root_.UpperTheory.V.Th.HasHeckeOperatorDense := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q
  refine ⟨2 * n.factorial, ?_⟩
  · skip
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => _root_.UpperTheory.V.Z.Win.locDataT_alt hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := _root_.UpperTheory.V.Th.opOfX_alt hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact ⟨A2, h2⟩
end
end

