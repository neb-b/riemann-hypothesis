module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopProd
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

private def dbl {G : Type} [Group G] (U : Subgroup G) (g : G) : Set (G ⧸ U) :=
  {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}

private theorem dbl_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (hU : CO U) (g : G) : (dbl U g).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem act_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {U : Subgroup G} {v : V} (hv : ∀ u ∈ U, ρ u v = v) {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk y) : ρ x v = ρ y v := by
  have h1 := hv _ (QuotientGroup.eq.1 h)
  calc ρ x v = ρ x (ρ (x⁻¹ * y) v) := by rw [h1]
    _ = ρ y v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]

private theorem mk_eq (U : ∀ i, Subgroup (G i)) (x y : ∀ i, G i) :
    (QuotientGroup.mk x : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk y ↔
      ∀ j, (QuotientGroup.mk (x j) : G j ⧸ U j) = QuotientGroup.mk (y j) := by
  simp [QuotientGroup.eq, Subgroup.mem_pi]

private noncomputable def pr (U : ∀ i, Subgroup (G i)) (j : Fin r) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : G j ⧸ U j :=
  QuotientGroup.mk (c.out j)

private theorem pr_mk (U : ∀ i, Subgroup (G i)) (j : Fin r) (x : ∀ i, G i) :
    pr U j (QuotientGroup.mk x) = QuotientGroup.mk (x j) :=
  (mk_eq U _ _).1 (QuotientGroup.out_eq' _) j

private theorem pr_ext (U : ∀ i, Subgroup (G i)) {c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U}
    (h : ∀ j, pr U j c = pr U j d) : c = d := by
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
  exact (mk_eq U _ _).2 h

private theorem mem_dbl (U : ∀ i, Subgroup (G i)) (g : ∀ i, G i) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    c ∈ dbl (Subgroup.pi Set.univ U) g ↔ ∀ j, pr U j c ∈ dbl (U j) (g j) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact ⟨u j, hu j trivial, pr_mk U j _⟩
  · intro h
    choose u hu he using h
    exact ⟨u, fun j _ => hu j, pr_ext U fun j => by rw [pr_mk]; exact he j⟩

private theorem mem_dbl_one {H : Type} [Group H] (U : Subgroup H) (c : H ⧸ U) :
    c ∈ dbl U 1 ↔ c = QuotientGroup.mk 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [QuotientGroup.eq] using hu
  · rintro rfl
    exact ⟨1, U.one_mem, by simp⟩

private noncomputable def glue (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    (∀ i, G i) ⧸ Subgroup.pi Set.univ U :=
  QuotientGroup.mk (Pi.mulSingle i (c.out i) * d.out)

private theorem pr_glue_same (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U)
    (hd : pr U i d = QuotientGroup.mk 1) : pr U i (glue U i c d) = pr U i c := by
  rw [glue, pr_mk]
  have := QuotientGroup.eq.1 hd
  simpa [pr, QuotientGroup.eq] using this

private theorem pr_glue_ne (U : ∀ i, Subgroup (G i)) {i j : Fin r} (h : j ≠ i)
    (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : pr U j (glue U i c d) = pr U j d := by
  rw [glue, pr_mk]
  simp [pr, Pi.mulSingle_eq_of_ne h]

private theorem hop_mul [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (hU : ∀ i, CO (U i))
    (i : Fin r) (x : G i) (b : ∀ i, G i) (hb : b i = 1) (v : V) (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v)
    (hw : ∀ u ∈ Subgroup.pi Set.univ U, ρ u (hopR ρ (Subgroup.pi Set.univ U) b v) = hopR ρ (Subgroup.pi Set.univ U) b v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x * b) v =
      hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
  have hW : CO (Subgroup.pi Set.univ U) :=
    ⟨isCompact_univ_pi fun j => (hU j).1, isOpen_set_pi Set.finite_univ fun j _ => (hU j).2⟩
  have hs : ∀ g w, hopR ρ (Subgroup.pi Set.univ U) g w = ∑ c ∈ (dbl_finite hW g).toFinset, ρ c.out w :=
    fun g w => finsum_mem_eq_finite_toFinset_sum _ (dbl_finite hW g)
  have ha : ∀ c ∈ dbl (Subgroup.pi Set.univ U) (Pi.mulSingle i x), ∀ j, j ≠ i → pr U j c = QuotientGroup.mk 1 := by
    intro c hc j hj
    have := (mem_dbl U _ c).1 hc j
    rwa [Pi.mulSingle_eq_of_ne hj, mem_dbl_one] at this
  have hb' : ∀ d ∈ dbl (Subgroup.pi Set.univ U) b, pr U i d = QuotientGroup.mk 1 := by
    intro d hd
    have := (mem_dbl U _ d).1 hd i
    rwa [hb, mem_dbl_one] at this
  have h1 : hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) =
      ∑ p ∈ (dbl_finite hW (Pi.mulSingle i x)).toFinset ×ˢ (dbl_finite hW b).toFinset,
        ρ (glue U i p.1 p.2).out v := by
    rw [hs (Pi.mulSingle i x), Finset.sum_product]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Set.Finite.mem_toFinset] at hc
    have e : ρ c.out (hopR ρ (Subgroup.pi Set.univ U) b v) =
        ρ (Pi.mulSingle i (c.out i)) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
      refine act_congr ρ hw ((mk_eq U _ _).2 fun j => ?_)
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact ha c hc j hj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, hs b, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact act_congr ρ hv (QuotientGroup.out_eq' _).symm
  rw [h1, hs]
  symm
  refine Finset.sum_bij (fun p _ => glue U i p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨c, d⟩ hp
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp ⊢
    refine (mem_dbl U _ _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [pr_glue_same U j c d (hb' d hp.2), Pi.mul_apply, hb, mul_one]
      exact (mem_dbl U _ _).1 hp.1 j
    · rw [pr_glue_ne U hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]
      exact (mem_dbl U _ _).1 hp.2 j
  · rintro ⟨c, d⟩ hp ⟨c', d'⟩ hp' h
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp hp'
    have h' : glue U i c d = glue U i c' d' := h
    refine Prod.ext (pr_ext U fun j => ?_) (pr_ext U fun j => ?_)
    · by_cases hj : j = i
      · subst hj
        rw [← pr_glue_same U j c d (hb' d hp.2), h', pr_glue_same U j c' d' (hb' d' hp'.2)]
      · rw [ha c hp.1 j hj, ha c' hp'.1 j hj]
    · by_cases hj : j = i
      · subst hj
        rw [hb' d hp.2, hb' d' hp'.2]
      · rw [← pr_glue_ne U hj c d, h', pr_glue_ne U hj]
  · intro e he
    rw [Set.Finite.mem_toFinset, mem_dbl] at he
    have hd : pr U i (QuotientGroup.mk (Function.update e.out i 1)) = QuotientGroup.mk 1 := by
      rw [pr_mk, Function.update_self]
    refine ⟨(QuotientGroup.mk (Pi.mulSingle i (e.out i)), QuotientGroup.mk (Function.update e.out i 1)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, mem_dbl]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [Pi.mul_apply, hb, mul_one] at this
          rw [pr_mk, Pi.mulSingle_eq_same j (Quotient.out e j)]
          exact this
        · rw [pr_mk, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, mem_dbl_one]
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [hd, hb, mem_dbl_one]
        · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul] at this
          rw [pr_mk, Function.update_of_ne hj]
          exact this
    · refine pr_ext U fun j => ?_
      by_cases hj : j = i
      · subst hj
        rw [pr_glue_same U j _ _ hd, pr_mk, Pi.mulSingle_eq_same]
        rfl
      · rw [pr_glue_ne U hj, pr_mk, Function.update_of_ne hj]
        rfl

private theorem hop_one {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    {U : Subgroup H} {v : V} (hv : ∀ u ∈ U, ρ u v = v) : hopR ρ U 1 v = v := by
  have h : dbl U 1 = {QuotientGroup.mk 1} := Set.ext fun c => mem_dbl_one U c
  change ∑ᶠ c ∈ dbl U 1, ρ c.out v = v
  rw [h, finsum_mem_singleton, act_congr ρ hv (QuotientGroup.out_eq' _), map_one, Module.End.one_apply]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopProd :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (Q : Submodule ℂ V), (∀ i, CO (U i)) →
      (∀ v ∈ Q, ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) → (∀ i g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i g) v ∈ Q) →
      ∀ g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
  intro r G _ _ _ V _ _ ρ U Q hU hfix hone
  have key : ∀ s : Finset (Fin r), ∀ g : ∀ i, G i, (∀ j, j ∉ s → g j = 1) →
      ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg v hv
      have : g = 1 := funext fun j => hg j (Finset.notMem_empty j)
      rw [this, hop_one ρ (hfix v hv)]
      exact hv
    | insert i s hi ih =>
      intro g hg v hv
      have hb : hopR ρ (Subgroup.pi Set.univ U) (Function.update g i 1) v ∈ Q := by
        refine ih _ (fun j hj => ?_) v hv
        by_cases hji : j = i
        · subst hji; exact Function.update_self ..
        · rw [Function.update_of_ne hji]
          exact hg j (by simp [hji, hj])
      have e : g = Pi.mulSingle i (g i) * Function.update g i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      rw [e, hop_mul ρ U hU i (g i) _ (Function.update_self ..) v (hfix v hv) (hfix _ hb)]
      exact hone i _ _ hb
  exact fun g => key Finset.univ g (fun j hj => absurd (Finset.mem_univ j) hj)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndTens
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_image {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Y] [Module ℂ Y]
    (f : G → Y) (hf : f ∈ GlobalTheory.PRep.smoothPart (rightReg ℂ G Y)) (K : Set G) (hK : IsCompact K) : (f '' K).Finite := by
  have hlc : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have ho : IsOpen {g : G | rightReg ℂ G Y g f = f} := hf
    have hc : Continuous fun y : G => x⁻¹ * y := by fun_prop
    have : (fun y : G => x⁻¹ * y) ⁻¹' {g : G | rightReg ℂ G Y g f = f} ∈ nhds x :=
      (ho.preimage hc).mem_nhds (by simp)
    filter_upwards [this] with y hy
    have h2 : f (x * (x⁻¹ * y)) = f x := congrFun hy x
    simpa using h2
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have := (hlc.comp_continuous (continuous_subtype_val (p := (· ∈ K)))).range_finite
  rwa [Set.range_comp, Subtype.range_coe_subtype] at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indTens :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (P K : Subgroup G) (ρ : Representation ℂ P V) (m : Representation ℂ Γ B), CO K →
      (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
      ∃ e : smoothPart (ind P ρ) ⊗[ℂ] B ≃ₗ[ℂ] IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤,
        ∀ a b g, (e (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ b := by
  intro G _ _ _ Γ _ V _ _ B _ _ P K ρ m hK hPK
  have hact : ∀ (p : P) (v : V) (b : B),
      ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (v ⊗ₜ[ℂ] b) = ρ p v ⊗ₜ[ℂ] b := by
    intro p v b
    simp [extTensor]
  let Φ₀ : GlobalTheory.PRep.smoothPart (ind P ρ) →ₗ[ℂ] B →ₗ[ℂ]
      IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ :=
    LinearMap.mk₂ ℂ (fun a b => ⟨fun g => a.1.1 g ⊗ₜ[ℂ] b, ⟨fun _ => trivial, fun h g => by
        rw [hact, ← a.1.2 h g]; rfl⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds a.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : a.1.1 (x * u) = a.1.1 x := congrFun (congrArg Subtype.val hu) x
        show a.1.1 (x * u) ⊗ₜ[ℂ] b = a.1.1 x ⊗ₜ[ℂ] b
        rw [h2]⟩)
      (fun a a' b => Subtype.ext (funext fun g => TensorProduct.add_tmul _ _ _))
      (fun c a b => Subtype.ext (funext fun g => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun a b b' => Subtype.ext (funext fun g => TensorProduct.tmul_add _ _ _))
      (fun c a b => Subtype.ext (funext fun g => TensorProduct.tmul_smul _ _ _))
  let Φ := TensorProduct.lift Φ₀
  have hΦ : ∀ a b g, (Φ (a ⊗ₜ b)).1 g = a.1.1 g ⊗ₜ[ℂ] b := fun a b g => rfl
  let β := Module.Basis.ofVectorSpace ℂ B
  let ES := TensorProduct.equivFinsuppOfBasisRight (M := GlobalTheory.PRep.smoothPart (ind P ρ)) β
  let EV := TensorProduct.equivFinsuppOfBasisRight (M := V) β
  have key : ∀ x i g, (ES x i).1.1 g = EV ((Φ x).1 g) i := by
    intro x i g
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [ES.map_zero, Φ.map_zero]
      change (0 : V) = EV 0 i
      rw [EV.map_zero]
      rfl
    | tmul a b =>
      rw [hΦ]
      simp only [ES, EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      rfl
    | add x y hx hy => simp [hx, hy]
  have hEV : ∀ (p : P) y i, EV (((extTensor ρ m).comp (MonoidHom.inl P Γ)) p y) i = ρ p (EV y i) := by
    intro p y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hact]
      simp only [EV, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩, hΦ⟩
  · refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    apply ES.injective
    ext i g
    rw [key, hx]
    change EV 0 i = 0
    rw [EV.map_zero]
    rfl
  · intro f
    have hlaw : ∀ (p : P) g, f.1 (p * g) = ((extTensor ρ m).comp (MonoidHom.inl P Γ)) p (f.1 g) := f.2.1.2
    let c : _ → GlobalTheory.PRep.smoothPart (ind P ρ) := fun i =>
      ⟨⟨fun g => EV (f.1 g) i, fun h g => by
          show EV (f.1 (h * g)) i = _
          rw [hlaw, hEV]⟩, by
        refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2.2 (by simp)) fun u hu => ?_)
        apply Subtype.ext
        funext x
        have h2 : f.1 (x * u) = f.1 x := congrFun hu x
        show EV (f.1 (x * u)) i = EV (f.1 x) i
        rw [h2]⟩
    have hfin : (Function.support c).Finite := by
      refine ((finite_image f.1 f.2.2 K hK.1).biUnion (t := fun y => ((EV y).support : Set _))
        fun y _ => Finset.finite_toSet _).subset fun i hi => ?_
      by_contra hn
      apply hi
      apply Subtype.ext
      apply Subtype.ext
      funext g
      obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
      have h0 : EV (f.1 k) i = 0 := by
        by_contra h0
        exact hn (Set.mem_biUnion ⟨k, hk, rfl⟩ (Finsupp.mem_support_iff.2 h0))
      show EV (f.1 (p * k)) i = 0
      rw [hlaw ⟨p, hp⟩ k, hEV, h0, map_zero]
    refine ⟨ES.symm (Finsupp.ofSupportFinite c hfin), Subtype.ext (funext fun g => EV.injective ?_)⟩
    ext i
    rw [← key, LinearEquiv.apply_symm_apply]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem pi_hom_ext {r : ℕ} {N : Fin r → Type} [∀ i, Monoid (N i)] {M : Type} [Monoid M]
    (f g : (∀ i, N i) →* M) (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g := by
  apply (MonoidHom.noncommPiCoprodEquiv (ι := Fin r) (N := N) (M := M)).symm.injective
  apply Subtype.ext
  funext i
  exact MonoidHom.ext fun x => h i x

private noncomputable def cfH {K : Type} [Field K] [NumberField K] {n : ℕ} (v : Pl K) : FA K n →* Gw n v where
  toFun := GM.cf v
  map_one' := by simp only [GM.cf]; rw [map_one, finAt_one]
  map_mul' a b := by simp only [GM.cf]; rw [map_mul, finAt_mul]

private theorem cf_ext {K : Type} [Field K] [NumberField K] {n : ℕ} {a b : FA K n}
    (h : ∀ v : Pl K, GM.cf v a = GM.cf v b) : a = b := by
  apply (AdelicGLn.finiteRestrictedEquiv K n).injective
  ext v : 1
  exact h v

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.embEx :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K), Function.Injective w → (∃ ι, IsEmb (n := n) w ι) ∧ ∀ ι : GS n w →* FA K n, IsEmb w ι →
      Continuous ι ∧ (∀ g i, GM.cf (w i) (ι g) = g i) ∧ (∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1) ∧
      (∀ h : FA K n, ∃ g h', h = ι g * h' ∧ ∀ i, GM.cf (w i) h' = 1) ∧ (∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h') ∧
      ∀ (U : ∀ v : Pl K, Subgroup (Gw n v)) (h : FA K n), h ∈ levOn (im w) U ↔
        ∃ g h', h = ι g * h' ∧ (∀ i, g i ∈ U (w i)) ∧ (∀ i, GM.cf (w i) h' = 1) ∧ ∀ v, GM.cf v h' ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  intro K _ _ n r w hw
  have L := fun v : Pl K => UpperTheory.ConvolutionTheory.Tf.locEmb K n v
  refine ⟨?_, ?_⟩
  · refine ⟨MonoidHom.noncommPiCoprod (fun i => AdelicGLn.localEmbedding (w i)) ?_, ?_⟩
    · intro i j hij x y
      exact (L (w i)).2.2.2.1 (w j) (fun e => hij (hw e).symm) x y
    · intro i g
      exact MonoidHom.noncommPiCoprod_mulSingle (N := fun i => Gw n (w i)) (fun i => AdelicGLn.localEmbedding (w i)) i g
  intro ι hι
  have hmul : ∀ (v : Pl K) (a b : FA K n), GM.cf v (a * b) = GM.cf v a * GM.cf v b :=
    fun v a b => map_mul (cfH v) a b
  have hinv : ∀ (v : Pl K) (a : FA K n), GM.cf v a⁻¹ = (GM.cf v a)⁻¹ :=
    fun v a => map_inv (cfH v) a
  have hone : ∀ v : Pl K, GM.cf v (1 : FA K n) = 1 := fun v => map_one (cfH v)
  have hcf : ∀ g i, GM.cf (w i) (ι g) = g i := by
    intro g i
    have e : (cfH (w i)).comp ι = Pi.evalMonoidHom (fun j => Gw n (w j)) i := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf (w i) (ι (Pi.mulSingle j x)) = (Pi.mulSingle j x : GS n w) i
      rw [hι j x]
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact (L (w j)).2.1 x
      · rw [Pi.mulSingle_eq_of_ne (Ne.symm h)]
        exact (L (w j)).2.2.1 (w i) (fun e => h (hw e).symm) x
    exact DFunLike.congr_fun e g
  have hoff : ∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1 := by
    intro g v hv
    have e : (cfH v).comp ι = 1 := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf v (ι (Pi.mulSingle j x)) = 1
      rw [hι j x]
      exact (L (w j)).2.2.1 v (fun e => hv (e ▸ Finset.mem_image_of_mem w (Finset.mem_univ j))) x
    exact DFunLike.congr_fun e g
  have hcomm : ∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h' := by
    intro g h' hh
    refine cf_ext fun v => ?_
    rw [hmul, hmul]
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hh i, one_mul, mul_one]
    · rw [hoff g v hv, one_mul, mul_one]
  have hsplit : ∀ h : FA K n, ∀ i, GM.cf (w i) ((ι fun j => GM.cf (w j) h)⁻¹ * h) = 1 := by
    intro h i
    rw [hmul, hinv, hcf, inv_mul_cancel]
  have hcont : Continuous ι := by
    let tr : Finset (Fin r) → GS n w → GS n w := fun s g i => if i ∈ s then g i else 1
    have hc : ∀ s : Finset (Fin r), Continuous fun g => ι (tr s g) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (fun g => ι (tr ∅ g)) = fun _ => 1 := by
          funext g
          have : tr ∅ g = 1 := by funext i; simp [tr]
          rw [this, map_one]
        rw [e]
        exact continuous_const
      | insert a s ha ih =>
        have e : (fun g => ι (tr (insert a s) g)) =
            fun g => ι (tr s g) * AdelicGLn.localEmbedding (w a) (g a) := by
          funext g
          rw [← hι a (g a), ← map_mul]
          congr 1
          funext i
          by_cases h : i = a
          · subst h
            simp [tr, ha]
          · simp [tr, h, Pi.mulSingle_eq_of_ne h]
        rw [e]
        exact ih.mul ((L (w a)).1.comp (continuous_apply a))
    have e : (fun g => ι (tr Finset.univ g)) = ι := by
      funext g
      congr 1
      funext i
      simp [tr]
    rw [← e]
    exact hc Finset.univ
  refine ⟨hcont, hcf, hoff, ?_, hcomm, ?_⟩
  · intro h
    exact ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, hsplit h⟩
  · intro U h
    constructor
    · intro hh
      have hh' : ∀ v, GM.cf v h ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := hh
      refine ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, fun i => ?_, hsplit h, fun v => ?_⟩
      · have := hh' (w i)
        rwa [if_pos (Finset.mem_image_of_mem w (Finset.mem_univ i))] at this
      · by_cases hv : v ∈ im w
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hsplit h i]
          exact one_mem _
        · have := hh' v
          rw [if_neg hv] at this
          rw [hmul, hinv, hoff _ v hv, inv_one, one_mul]
          exact this
    · rintro ⟨g, h', rfl, hg, h1, hint⟩
      have hh' : ∀ v, GM.cf v (ι g * h') ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := by
        intro v
        rw [hmul]
        by_cases hv : v ∈ im w
        · rw [if_pos hv]
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hcf, h1 i, mul_one]
          exact hg i
        · rw [if_neg hv, hoff g v hv, one_mul]
          exact hint v
      exact hh'
end

