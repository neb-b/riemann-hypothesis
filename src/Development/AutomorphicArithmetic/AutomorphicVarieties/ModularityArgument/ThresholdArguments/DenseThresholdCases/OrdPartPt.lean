module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PartPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TClParts

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Ord
private theorem ord_parts {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop}
    (hP : _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) (hs : H.IsSpec θ ι x.toRingHom lam ξ c0 sp) (hlam : lam ∈ H.admitted) (K : H.Lev) :
    H.OrdAt θ ι x.toRingHom lam ξ K c0 =
      ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
  have decomposeGeneralizedEigenspace {M : Type} [AddCommGroup M] [Module ℂ M] {κ : Type 1} (Y : κ → Submodule ℂ M) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (T : Module.End ℂ M)
      (hW : ∀ y ∈ W, T y ∈ W) (hY : ∀ i, ∀ y ∈ Y i, T y ∈ Y i) (h : W ≤ ⨆ i, Y i ⊓ W) (μ : ℂ) :
      W ⊓ T.maxGenEigenspace μ ≤ ⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ) := by
    have h1 : ∀ i, Y i ⊓ W ≤ ⨆ ν, (Y i ⊓ W) ⊓ T.maxGenEigenspace ν := fun i => by
      have : FiniteDimensional ℂ (Y i ⊓ W : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_right
      have hm : ∀ y ∈ Y i ⊓ W, T y ∈ Y i ⊓ W := fun y hy => ⟨hY i y hy.1, hW y hy.2⟩
      have h0 := congrArg (Submodule.map (Y i ⊓ W).subtype) (Module.End.iSup_maxGenEigenspace_eq_top (T.restrict hm))
      rw [Submodule.map_iSup, Submodule.map_subtype_top] at h0
      refine h0.ge.trans (iSup_mono fun ν => ?_)
      exact (Submodule.inf_genEigenspace T (Y i ⊓ W) hm).ge
    have h2 : W ≤ (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ⊔ ⨆ ν ≠ μ, T.maxGenEigenspace ν := by
      refine h.trans (iSup_le fun i => (h1 i).trans (iSup_le fun ν => ?_))
      by_cases hν : ν = μ
      · subst hν
        rw [inf_assoc]
        exact le_sup_of_le_left (le_iSup (fun i => Y i ⊓ (W ⊓ T.maxGenEigenspace ν)) i)
      · exact le_sup_of_le_right (inf_le_right.trans (le_iSup₂ (f := fun ν (_ : ν ≠ μ) => T.maxGenEigenspace ν) ν hν))
    have h3 : (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ≤ T.maxGenEigenspace μ :=
      iSup_le fun i => inf_le_right.trans inf_le_right
    refine (inf_le_inf_right _ h2).trans ?_
    rw [sup_inf_assoc_of_le _ h3, (T.independent_maxGenEigenspace μ).symm.eq_bot, sup_bot_eq]

  have uOp_preserves {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] (I : Iwa G) (π : Representation ℂ G M) (a : G) (Y : Submodule ℂ M)
      (hY : ∀ g, ∀ y ∈ Y, π g y ∈ Y) : ∀ y ∈ Y, I.uOp π a y ∈ Y := by
    unfold Iwa.uOp
    refine finsum_induction (fun φ : Module.End ℂ M => ∀ y ∈ Y, φ y ∈ Y) (fun y _ => by simp)
      (fun φ ψ h h' y hy => add_mem (h y hy) (h' y hy)) fun q => hY _

  let stabilizer {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) : Subgroup G := {
    carrier := {g | π g y = y}
    one_mem' := by simp
    mul_mem' {a b} (ha : π a y = y) (hb : π b y = y) := by
      change π (a * b) y = y
      rw [map_mul, mul_apply_eq_comp, hb, ha]
    inv_mem' {a} (ha : π a y = y) := by
      change π a⁻¹ y = y
      conv_lhs => rw [← ha]
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl }

  have mem_fixed_iff {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) (U : Subgroup G) :
      y ∈ fixd π U ↔ U ≤ stabilizer π y := Iff.rfl

  have commuteActions (u : H.X.Ub) (b : GV n H.Sl) (F : Fin H.m → H.X.Fn ℂ d) :
      H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m b F) = H.X.rpF ℂ d H.m b (H.X.raF d (H.τC ι) u F) := by
    ext i g k
    change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * ((u : H.Ga), 1) * (1, b)) k) i =
      ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * (1, b) * ((u : H.Ga), 1)) k) i
    simp [mul_assoc]

  have preserveFixed (U : Subgroup H.X.Ub) (b : GV n H.Sl) :
      ∀ F ∈ fixd (H.X.raF d (H.τC ι)) U, H.X.rpF ℂ d H.m b F ∈ fixd (H.X.raF d (H.τC ι)) U := fun F hF u hu => by
    rw [commuteActions, hF u hu]

  have preserveBig (b : GV n H.Sl) :
      ∀ F ∈ H.Big ι ξ, H.X.rpF ℂ d H.m b F ∈ H.Big ι ξ := fun F hF => by
    refine ⟨fun i hi γ g => ?_, preserveFixed _ b F hF.2⟩
    have := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at this
    exact this

  have memClassical (F : Fin H.m → H.X.Fn ℂ d) : F ∈ H.ClAt θ ι x.toRingHom lam ξ K c0 ↔
      F ∈ H.Big ι ξ ∧ F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) ∧ F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N ∧
        F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm c0) ∧ ∀ v i y,
        H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := by
    simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, and_assoc]

  have fixedByIwahori (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K c0) :
      F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 c0) := by
    classical
    obtain ⟨-, -, h1, h2, h3⟩ := (memClassical F).1 hF
    rw [mem_fixed_iff] at h1 h2 ⊢
    refine sup_le (sup_le h1 fun t ht => ?_) h2
    refine Subgroup.pi_mem_of_mulSingle_mem t fun v => ?_
    have htv : t v ∈ (glIwa ((H.Sl v).adicCompletion L) n).Tc c0 := ht v trivial
    obtain ⟨y, hy, hy'⟩ := (glBridge ((H.Sl v).adicCompletion L) n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.2.2.2.2
      ⟨t v, (glIwa _ n).Tc_le c0 htv⟩
    have hy1 : t v = _ := hy
    rw [hy1]
    change MonoidHom.mulSingle (fun v : H.V => GLw n (H.Sl v)) v _ ∈ _
    rw [map_list_prod, List.map_ofFn]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    have := h3 v i (y i)
    rw [hs.triv v i (y i) (hy' c0 htv i), map_one, inv_one, one_smul] at this
    exact this

  have preserveClassical (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K c0) :
      H.uzC ι lam d F ∈ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    refine Submodule.smul_mem _ _ ?_
    have h0 := (uOpLevel _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) c0).1 _ H.X.I.z_mem F (fixedByIwahori F hF)
    obtain ⟨hb, hl, h1, h2, h3⟩ := (memClassical F).1 hF
    refine (memClassical _).2 ⟨uOp_preserves _ _ _ _ preserveBig F hb, uOp_preserves _ _ _ _ (preserveFixed _) F hl,
      fun u hu => h0 u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)), fun u hu => h0 u (Subgroup.mem_sup_right hu),
      fun v i y => ?_⟩
    rw [(uOpMul _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) _ _ H.X.I.z_mem H.X.I.z_mem F h1).2.2.2.1 _ (eV n H.Sl v i y).2, h3, map_smul]

  have h1 : H.ClAt θ ι x.toRingHom lam ξ K c0 ≤
      ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    intro F hF
    have hF' := (memClassical F).1 hF
    exact _root_.classical_in_iwahori_parts H ι θ _ lam ξ K c0 hH (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨c0, fixedByIwahori F hF⟩)
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)
  have := hs.fin K c0 le_rfl
  have h2 := decomposeGeneralizedEigenspace (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K c0) (H.uzC ι lam d)
    preserveClassical (fun Y => _root_.classical_parts_commute H ι lam ξ Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K c0 :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)

open TensorProduct in
set_option maxHeartbeats 800000 in
theorem ordinary_pt_of_literal_automorphy_n : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.PartPtAlt := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ y hy
  have : Finite (ResidueField c.O) := by
    have : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    have : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hComm, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  have := (hK a).2.1
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem
    A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) hComm

  let Y₀ := H.X.Ord (H.τA A) θ (H.lev K)
  let Y₁ := H.MK θ a K
  let W := Fin H.m → H.X.Fn ℂ d
  let χ := ι.toRingHom.comp x.toRingHom
  let : Algebra A ℂ := χ.toAlgebra
  let : Module A W := Module.compHom W χ
  have : IsScalarTower A ℂ W := ⟨fun b z F => mul_smul (χ b) z F⟩
  let s : Y₀ →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hsp.add K _ f.2 _ g.2
      map_smul' := fun b f => hsp.smul K _ f.2 b }
  let baseChange := s.liftBaseChange ℂ
  have hs : Function.Injective baseChange := by
    let b := Module.Free.chooseBasis A Y₀
    have hb : baseChange = Finsupp.linearCombination ℂ (fun i => sp (b i)) ∘ₗ
        (b.baseChange ℂ).repr.toLinearMap :=
      (b.baseChange ℂ).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
          Finsupp.linearCombination_single, Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [hb, LinearMap.coe_comp]
    exact Function.Injective.comp (hsp.indep K _ b) (b.baseChange ℂ).repr.injective
  let O := LinearMap.range baseChange
  have hO : O = H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
    change LinearMap.range (s.liftBaseChange ℂ) = _
    rw [LinearMap.range_liftBaseChange, ← hsp.span K c0 le_rfl, Set.image_eq_range]
    rfl
  have : FiniteDimensional ℂ O := Module.Finite.equiv (LinearEquiv.ofInjective baseChange hs)
  let op₀ (i : H.Op) : Module.End A Y₀ := (H.op A i).restrict (hComm.1 i)
  have intertwines (i : H.Op) : H.opC ι lam d i ∘ₗ baseChange =
      baseChange ∘ₗ (op₀ i).baseChange ℂ := by
    refine TensorProduct.AlgebraTensorModule.ext fun z f => ?_
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
      baseChange, map_smul]
    exact congrArg (z • ·) (hsp.op K i _ f.2).symm
  let Ψ := LinearEquiv.ofInjective baseChange hs
  let opO (i : H.Op) : Module.End ℂ O :=
    (Ψ.conjRingEquiv : Module.End ℂ (ℂ ⊗[A] Y₀) ≃+* Module.End ℂ O) ((op₀ i).baseChange ℂ)
  have opO_apply (i : H.Op) (F : O) : (opO i F : W) = H.opC ι lam d i F := by
    obtain ⟨v, rfl⟩ := Ψ.surjective F
    change (Ψ ((op₀ i).baseChange ℂ (Ψ.symm (Ψ v))) : W) = H.opC ι lam d i (Ψ v : W)
    rw [Ψ.symm_apply_apply]
    exact (LinearMap.congr_fun (intertwines i) v).symm
  have opO_commute (i j : H.Op) : Commute (opO i) (opO j) := by
    have hc : Commute (op₀ i) (op₀ j) :=
      LinearMap.ext fun f => Subtype.ext (hComm.2 i j f f.2)
    exact (hc.map (Module.End.baseChangeHom A ℂ Y₀)).map Ψ.conjRingEquiv

  let incl : Y₁ →ₗ[A] Y₀ := Submodule.inclusion inf_le_left
  let proj : Y₀ →ₗ[A] Y₁ := LinearMap.codRestrict _ (Y₀.subtype ∘ₗ e)
    (fun f => (hY _).2 (LinearMap.congr_fun hi.eq f))
  have hproj : proj ∘ₗ incl = LinearMap.id :=
    LinearMap.ext fun f => Subtype.ext
      (congrArg (fun g : Y₀ => (g : H.X.Fn A H.m)) ((hY (incl f)).1 f.2))
  have hincl : Function.Injective (incl.baseChange ℂ) := by
    refine Function.LeftInverse.injective (g := proj.baseChange ℂ) fun v => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hproj,
      LinearMap.baseChange_id, LinearMap.id_apply]
  let z : H.TK θ a K →ₐ[A] ℂ :=
    { toRingHom := ι.toRingHom.comp y.toRingHom
      commutes' := fun b => congrArg ι (RingHom.congr_fun hy b) }
  obtain ⟨v, hv, hvEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig
    (M := ↥(H.MK θ a K)) z
  let F := Ψ (incl.baseChange ℂ v)
  have hF : F ≠ 0 := fun h => hv (hincl (Ψ.map_eq_zero_iff.mp h))
  have hEig (i : H.Op) : opO i F = z (H.gen θ a K i) • F := by
    have hi : op₀ i ∘ₗ incl = incl ∘ₗ Algebra.lsmul A A Y₁ (H.gen θ a K i) :=
      LinearMap.ext fun f => Subtype.ext rfl
    have Hbase := LinearMap.congr_fun (congrArg (fun f : Y₁ →ₗ[A] Y₀ => f.baseChange ℂ) hi) v
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      hvEig, map_smul] at Hbase
    change Ψ ((op₀ i).baseChange ℂ (Ψ.symm (Ψ (incl.baseChange ℂ v)))) = _
    rw [Ψ.symm_apply_apply, Hbase, map_smul]

  let J := {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}
  let Z (j : J) := j.1.Y.comap O.subtype
  have hZ : ⨆ j, Z j = ⊤ := by
    apply Submodule.map_injective_of_injective O.subtype_injective
    rw [Submodule.map_iSup, Submodule.map_subtype_top]
    simp_rw [Z, Submodule.map_comap_subtype, inf_comm O]
    exact (hO.symm ▸ ord_parts H hH θ ι hP x lam d ξ c0 sp hsp hlam K).symm
  have stable (j : J) (i : H.Op) (G : O) (hG : G ∈ Z j) : opO i G ∈ Z j := by
    change (opO i G : W) ∈ j.1.Y
    rw [opO_apply]
    exact _root_.hecke_operator_preserves_part H ι lam ξ j.1 i G hG
  obtain ⟨φ, hφ, hφEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig
    opO opO_commute (fun i => z (H.gen θ a K i)) F hF hEig
  obtain ⟨j, hj⟩ : ∃ j, φ ∘ₗ (Z j).subtype ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hφ (LinearMap.ker_eq_top.1 (top_le_iff.1 (hZ ▸ iSup_le fun j G hG => ?_)))
    exact LinearMap.congr_fun (hn j) ⟨G, hG⟩
  obtain ⟨G, hG, hGEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot
    (fun i => (opO i).restrict (stable j i))
    (fun i k => LinearMap.ext fun G => Subtype.ext (LinearMap.congr_fun (opO_commute i k).eq G))
    (fun i => z (H.gen θ a K i)) _ hj (fun i G => hφEig i G)
  refine ⟨j.1, G, j.2, fun h => hG (Subtype.ext (Subtype.ext h)), ⟨G.2, hO ▸ G.1.2⟩, fun i => ?_⟩
  rw [← opO_apply]
  exact congrArg (fun f : Z j => (f.1 : W)) (hGEig i)

end UpperTheory.V.Z.Ord
end
