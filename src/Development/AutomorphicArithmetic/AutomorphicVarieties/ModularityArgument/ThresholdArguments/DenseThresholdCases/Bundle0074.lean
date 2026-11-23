module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.LevelU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UmodAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0071
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0072
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WJTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BaseObjectHomExt
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
attribute [local instance 2000] UpperTheory.V.W.coefLocal
open UpperTheory.V.Hi.LvR
private theorem base_object_hom_ext {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (T : Type) [CommRing T] [Algebra O T] [Alg.IsCO O T] (f g : B.B →ₐ[O] T)
    (h1 : B.u.D.map f.toRingHom = B.u.D.map g.toRingHom)
    (h2 : ∀ v i, W.pushCh f.toRingHom (B.u.ψ v i) = W.pushCh g.toRingHom (B.u.ψ v i)) : f = g := by
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l F O n r B.B T g B.u
  exact (B.univ T p).unique ⟨h1.trans hp.1, fun v i => (h2 v i).trans (hp.2 v i)⟩ hp
private theorem lam_val {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) (v : F.Vl) (i : Fin n)
    (γ : F.Gv v) (hγ : γ ∈ F.Iv v) (a : O) (x : Λ.Λ) (hx : x = algebraMap O Λ.Λ a * (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) - 1) :
    Λ.toPair p x = algebraMap O R a * (p.ψ v i γ : R) - 1 := by
  have e : Λ.toPair p (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) = (p.ψ v i γ : R) :=
    by have h := congrArg Units.val (DFunLike.congr_fun (Λ.toPair_spec r p v i) (⟨γ, hγ⟩ : F.Iv v)); exact h
  rw [hx, map_sub, map_mul, map_one, AlgHom.commutes, e]
private theorem eq_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (P N N₀ : Submodule A M) (Z : Submodule A P)
    (h : Z.map P.subtype = N) (h₀ : ∀ f, f ∈ N ↔ f ∈ N₀) :
    ∃ e : Z ≃+ N₀, ∀ z : Z, (e z : M) = (z : P) ∧ ((z : P) : M) ∈ N := by
  have e2 : Z.map P.subtype = N₀ := h.trans (Submodule.ext h₀)
  exact ⟨((Z.equivMapOfInjective P.subtype P.injective_subtype).trans (LinearEquiv.ofEq _ _ e2)).toAddEquiv,
    fun z => ⟨rfl, h ▸ Submodule.mem_map_of_mem z.2⟩⟩
private theorem under_eq {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver A w) (hv : IsPlaceOver A v) :
    w.under (𝓞 (Lp L)) = v := by
  ext x
  exact (hw (algebraMap _ (𝓞 L) x)).symm.trans (hv x)
private def ProjAt {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (U U₁ : Subgroup G) [(U₁.subgroupOf U).Normal] : Prop :=
  ∃ ρ' : Representation A (U ⧸ U₁.subgroupOf U) (fixd ρ U₁), (∀ (u : U) f, (ρ' (u : U ⧸ U₁.subgroupOf U) f).1 = ρ u.1 f) ∧
    Module.Projective (MonoidAlgebra A (U ⧸ U₁.subgroupOf U)) ρ'.asModule
set_option maxHeartbeats 3200000 in
private theorem s3 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev) (B : UniversalOrdinaryDeterminantRing r) (β : B'.B →ₐ[c.O] B.B) (hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h))
    (hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i))
    (μ : B.B →+* Module.End A ((hset Q0 τ₀).MK θ a K0))
    (hμ : (hset Q0 τ₀).MK θ a K0 = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q0 τ₀).MK θ a K0) ((hset Q0 τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q0 τ₀).TK θ a K0)) (f : B.B →ₐ[c.O] (hset Q0 τ₀).TK θ a K0), (hset Q0 τ₀).IsMap θ a K0 B.u.D B.u.ψ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q0 τ₀).MK θ a K0))) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M) (ρ : Representation A (GV n Q.wq) M) (α : B'.B →+* Module.End A M) (lam : A →ₐ[c.O] B'.B), (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧
      (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      (∀ K : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → Module.Finite A (fixd ρ (Subgroup.pi Set.univ K))) ∧
      (∀ K K' : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → (∀ q, IsOpen (K' q : Set (GLw n (Q.wq q))) ∧ IsCompact (K' q : Set (GLw n (Q.wq q)))) → ∀ [((Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K)).Normal], (∀ q, K' q ≤ K q) → ProjAt ρ (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ K')) ∧
      (∃ e0 : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n)) ≃+ (hset Q0 τ₀).MK θ a K0, ∀ t (x x' : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n))), (x' : M) = α t x → e0 x' = μ (β t) (e0 x)) ∧
      ∀ z : M, z ≠ 0 → ∃ (x : B'.B →+* Qbar l) (ρx : V.frame.G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n Q.wq) Y) (sp : M →+ Y) (σ : ∀ q, SmIrr (GLw n (Q.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ B'.u.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (Q.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (Q.wq q)) (rc : IrrGL (k := (Q.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ q))) := by
  obtain ⟨θ', a', lam, hw', e1, e2, hl, hd, hJ⟩ := _root_.UpperTheory.V.Hi.LvW.step1_alt P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B'
  obtain ⟨hop, hM⟩ := _root_.UpperTheory.V.Hi.LvW.step2_alt P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B' hS K0 θ' a' e1 e2
  obtain ⟨ρ, α, h1, h2, h3, h4, h5, h6⟩ := @_root_.UpperTheory.V.Hi.LvW.umodAbs_alt P.litN L Ω _ _ _ _ _ l _ n c (hset Q τ₀) (_root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀) A _ _ _ θ' hw' a' dq ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties (rUp h) ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor P l L Ω s n hn V Q c (rUp h) ι m τ₀ (_root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty)) (fun _ => ⟨0, fun _ _ _ => le_rfl⟩) trivial (hd _) (neatU l L Ω s n hn V Q c m τ₀)
    (levelUR2Faith l L Ω s n hn V Q c m τ₀) B'.B _ _ B'.u.D B'.u.ψ lam (base_object_hom_ext B') hJ
  have key := _root_.UpperTheory.V.Hi.levelUR2SmulKey_alt P.litN l L Ω s n hn V0 V Q0 Q c m τ₀ A θ hw a K0 (kMax Q τ₀)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) (fun _ _ => ⟨_, rfl⟩)
    θ' a' hw' e1 e2 hop hM B.B B'.B B.u.D B.u.ψ B'.u.D B'.u.ψ β hβ1 hβ2
    (base_object_hom_ext B') μ hμ (fun t y => (α t ⟨y.1, Submodule.mem_iSup_of_mem _ y.2⟩).1) (fun t => congrArg Subtype.val (map_zero (α t)))
    (fun {i1} {i2} => (@h5 (kMax Q τ₀) i1 i2).elim fun f hf => ⟨f, hf.1, fun t y => hf.2 t y _ rfl⟩)
  have h4' : ∀ (K K' : (hset Q τ₀).Lev) [((Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)).Normal], (∀ q, K'.1 q ≤ K.1 q) → ProjAt ρ (Subgroup.pi Set.univ K.1) (Subgroup.pi Set.univ K'.1) :=
    fun K K' _ hle => h4 K K' hle
  obtain ⟨e0, he0⟩ := eq_sub _ _ ((hset Q0 τ₀).MK θ a K0) _ (h3 (kMax Q τ₀)).1 hM
  refine ⟨_, _, _, ρ, α, lam, hl, h1, h2, fun K hK => (h3 ⟨K, hK⟩).2, fun K K' hK hK' hN hle => @h4' ⟨K, hK⟩ ⟨K', hK'⟩ hN hle, ⟨e0, fun t x x' hx => Subtype.ext ?_⟩, h6⟩
  exact ((he0 x').1.trans (congrArg Subtype.val hx)).trans (key t ⟨x.1.1, (he0 x).2⟩ (e0 x) (he0 x).1.symm)
set_option maxHeartbeats 1600000 in
private theorem s4 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (B : UniversalOrdinaryDeterminantRing r) (K : (hset Q0 τ₀).Lev) (hS : V0.S' = s.S) (J : Ideal B.B)
    (hJ : (hset Q0 τ₀).IsJ θ a K B.u.D B.u.ψ (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u : A →ₐ[c.O] B.B) J) : _root_.UpperTheory.V.Pa.LevelAlt B J := by
  have hN := P.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hA0 := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V0 Q0 c m τ₀
  obtain ⟨wv, e, hwt⟩ : ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] A), ∀ k, ∃ hγ : wt.γ k ∈ V0.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O A (wt.c k) * (κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Aˣ) - 1 :=
    levelUR2WtVars l L Ω s n V0 c r B ⟨A, κ, hi, hu⟩ (W.locCFT hN.aut.art hC l L Ω s)
  choose hγ hres hX using hwt
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := levelUR2BaseAct L Ω l n c _ hA0 A θ hw a K B.B B.u.D B.u.ψ _ J hJ
  obtain ⟨-, hfin, hfree⟩ := (hiComm L Ω l n c _ hA0 A θ hw K).2.2.2 a
  obtain ⟨b, eb, hb, heb⟩ := levelUR2BasePack l L Ω s V0 c.O n r B J _ wv A e (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u) hres
    (fun k => lam_val ⟨A, κ, hi, hu⟩ B.u _ _ _ (hγ k) _ _ (hX k)) _ μ hμ1 hμ2
  subst hb
  refine ⟨b, fun V h q v w Bq hp hv hvS hV hw' hBv _ => ?_⟩
  obtain rfl : (fun j => (w j).under (𝓞 (Lp L))) = v := funext fun j => under_eq (hw' j) (hBv j)
  have hsub : V0.S' ⊆ V.S' := hS ▸ V.sub
  obtain ⟨p', hp1, hp2⟩ := pairUp h hn hp B.u
  obtain ⟨B'⟩ := W.b0Ex (W.phiAll hC) l L Ω s V c n (rUp h) B.B ⟨p'⟩
  obtain ⟨β, hβ, -⟩ := B'.univ B.B p'
  have hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h) := hβ.1.trans hp1
  have hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i) :=
    fun v i => (hβ.2 v i).trans (hp2 v i)
  obtain ⟨M, _, _, ρ, α, lam, hl, h1, h2, h3, h4, ⟨e0, he0⟩, h6⟩ := @s3 P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι A _ _ _ κ hi hu m τ₀ ty θ th hw a rs
    V h (qUp V w hv hvS hV) (instDecidableEqFin q) hsub hp B' hS K B β hβ1 hβ2 μ hμ3
  obtain ⟨hI, hNm⟩ := levelUR2IwLev l L n q w
  have h4w : @ProjAt A (GV n w) M _ _ _ _ ρ (Pa.UIw n w) (Pa.UIw1 l n w) hNm :=
    @h4 (fun j => AlgebraTools.iwC _ n ⊤) (fun j => AlgebraTools.iwC _ n (Pa.ellC l _)) (fun j => ⟨(hI j ⊤).1, (hI j ⊤).2.1⟩)
      (fun j => ⟨(hI j _).1, (hI j _).2.1⟩) hNm fun j => (hI j _).2.2
  obtain ⟨ρ', h7, h8⟩ := h4w
  refine @_root_.UpperTheory.V.Hi.levelUR2ModPack_alt l _ L Ω _ _ _ _ _ _ s V0 c.O _ _ _ n r B J _ b V h q w (rN h) (rN_compat h) B'.B _ _ _ (pairN h B'.u)
    A _ _ e lam (fun k => ?_) β ⟨hβ1, hβ2⟩ M _ _ ρ α h1 h2
    (h3 (fun j => AlgebraTools.iwC _ n (Pa.ellC l _)) fun j => ⟨(hI j _).1, (hI j _).2.1⟩) hNm ρ' h7 h8 (e0.trans eb)
    (fun t x x' hx => (congrArg eb (he0 t x x' hx)).trans (heb (β t) (e0 x))) ι h6
  rw [hX k, map_sub, map_mul, map_one, AlgHom.commutes]
  exact congrArg (fun z => algebraMap c.O B'.B (b.wt.c k) * z - 1) (hl (b.wt.v k) (b.wt.i k) (b.wt.γ k) (hγ k))
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.level_of_isJ_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → _root_.UpperTheory.V.Pa.LevelAlt B J := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι B Λ R K hS J hJ
  obtain ⟨A, κ, hi, hu⟩ := Λ
  obtain ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ := R
  exact s4 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs B K hS J hJ
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndoscopyRank2Ordinary
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
private theorem coreA (H : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L]
    [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V}
    {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    (hS : V.S' = s.S) {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧
      (Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr)) ∧ x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι _
    (_root_.UpperTheory.Gal.projectedFormsSystemPart.autAway_alt H hL hC s hn V Q c r ι R.m R.τ₀ R.type hS) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  let y := AlgHom.liftOfSurjective f hsurj x hx
  have hy (b : B.B) : y (f b) = x b := AlgHom.liftOfSurjective_apply f hsurj x hx b
  have hΛ : y.toRingHom.comp (algebraMap Λ.Λ _) = (x.comp (Λ.toPair B.u)).toRingHom :=
    RingHom.ext fun b => (congrArg y (hlam b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam (Set.mem_univ _) y (hΛ ▸ har)
  refine ⟨ρ, hc, hs, hP, ?_⟩
  have hxy : (x : B.B →+* Qbar l) = y.toRingHom.comp f.toRingHom :=
    RingHom.ext fun b => (hy b).symm
  have e3 : x.D = W.GDet.ofRep (W.mat ρ) := by
    change B.u.D.map (x : B.B →+* Qbar l) = _
    rw [hxy]
    exact hD
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
theorem UpperTheory.Gal.projectedFormsSystemPart.irrArithPointsAutomorphicAway_of_isJ (H : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) (hE : _root_.UpperTheory.V.Z.Ord.EndOrdAlt) (hB : BornJ) :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → IrrArithPointsAutomorphicAway B ι J := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x h ρ hx ha hρ hi
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨ρ₀, -, hs, hP, hr⟩ := coreA H hL hC hn hS hJ x h hx ha
  have hss : IsSSRep ρ := by
    intro M hM
    rcases hi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot (Qbar l)).1 hv]
      simp
  have hss₀ : IsSSRep (ρ₀.comp V.pr) := by
    intro M hM
    have hInv : IsInv ρ₀ M := fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hM g
    obtain ⟨M', hM', hcompl⟩ := hs M hInv
    exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
  have e : Af.RepIso (ρ₀.comp V.pr) ρ := by
    have hD := hρ.symm.trans hr
    obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat ρ) (W.mat (ρ₀.comp V.pr)) hss hss₀ fun g => by
      rw [← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g,
        ← (AlgebraTools.Det.repApi (W.mat (ρ₀.comp V.pr))).2.1 g, hD]
    refine ⟨P, fun g => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    exact Units.ext (hP g).symm
  have hi₀ : Af.IsIrr (ρ₀.comp V.pr) := by
    obtain ⟨P, hconj⟩ := e.symm'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let E := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hInv : IsInv ρ (M.comap E.toLinearMap) := fun g v hv => by
      have hmem := hM g _ hv
      change ((ρ₀.comp V.pr) g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec
        ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ M at hmem
      change (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec _ ∈ M
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hconj g, inv_mul_cancel_right,
        Units.val_mul, ← Matrix.mulVec_mulVec] at hmem
    have hmap : M = (M.comap E.toLinearMap).map E.toLinearMap :=
      (Submodule.map_comap_eq_of_surjective E.surjective M).symm
    rcases hi.2.2 _ le_top hInv with hbot | htop
    · left
      rw [hmap, hbot, Submodule.map_bot]
    · right
      rw [hmap, htop, Submodule.map_top, LinearEquiv.range]
  obtain ⟨π, h1, h2, h3, h4⟩ := hP hi₀
  have h5 : Af.AttC ι ρ π := ⟨hss, h3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩
  refine ⟨⟨π, h1, h2, h5⟩, fun hc => ?_⟩
  have hRing : B.RingProps Λ J := _root_.UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data
    H l L Ω s n hn V Q c r ι B Λ R K hS J hJ
  have born := hB l L Ω s n hn V c r ι B Λ J hRing
    (hE l L Ω s n hn V Q c r ι B Λ R K J hJ) x h ρ hx ha hρ hi hc
  refine ⟨fun v hv hu => (born v hv hu).1, fun π' _ p => ?_⟩
  obtain ⟨t, ht⟩ := ImaginaryQuadraticEtaCharacter.winOf L n hn π'
  refine ⟨t, fun v hv0 hv => ?_⟩
  have k : TU π' v := by
    by_cases hl : ((l : ℕ) : 𝓞 L) ∈ v.asIdeal
    · refine (born v hl fun A hA => ?_).2 π' p
      obtain ⟨κ, k1, k2⟩ := hv.resolve_left (fun a => a hl) A hA
      exact ⟨κ, k1, fun i j e => k2 i j 1 le_rfl (by rw [e])⟩
    · exact tu_same hn h5 p (h4 v hl hv0)
  exact ht v k.1 k.2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTwA
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
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.twisted_point_property_of_isJ_arith_rep_autCsd :
    _root_.UpperTheory.V.Af.HypothesesH' → Z.Desc.DescWeak → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J →
    ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), 2 ≤ n → n ≤ 4 → x.Arith h →
    x.IsRep ρ → Continuous ρ → IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) →
    (∀ v : Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v) ∧
      ∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    J ≤ RingHom.ker x :=
  fun PH => _root_.UpperTheory.V.Z.Desc.W.point_property_of_isJ_arith_rep_autCsd (_root_.UpperTheory.Gal.SV.rowOf' PH.litN.aut.gal) PH
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JTwistA
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
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Desc.W.twistOk_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.TwistOk J :=
  _root_.UpperTheory.V.Z.Desc.W.jTwist_of_alt typeGd _root_.UpperTheory.V.Z.Desc.W.twist_away_statement _root_.UpperTheory.V.Z.Desc.W.sphUntw_alt ordTw _root_.UpperTheory.V.Z.Desc.W.principal_series_full_statement
end
end

