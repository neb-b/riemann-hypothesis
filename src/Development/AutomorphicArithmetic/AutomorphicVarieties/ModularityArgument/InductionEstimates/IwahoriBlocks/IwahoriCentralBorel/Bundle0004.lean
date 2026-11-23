module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.AdelicGluing.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TwoAtCharZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndStep
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indStep :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (P : Subgroup G) (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) (f : V →ₗ[ℂ] Y), LocOk P ρ →
      y.IsIrreducible → f ≠ 0 → (∀ p v, f (ρ p v) = y (p, 1) (f v)) →
      SimpleG (IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤) fun c : Γ => y (1, c) := by
  intro G _ _ _ Γ _ V _ _ Y _ _ P ρ y f hL hy hf hfe
  obtain ⟨B, _, _, m, e, hm, he⟩ := tensIso ρ y f hL.irr hL.schur hy hf hfe
  obtain ⟨K, hK, hPK⟩ := hL.iwa
  obtain ⟨E, hE⟩ := indTens P K ρ m hK hPK
  have hirr := (tensSimple (smInd P ρ) m hL.indIrr hL.indSchur hm).1
  let L : GlobalTheory.PRep.smoothPart (ind P ρ) ⊗[ℂ] B →ₗ[ℂ] (G → Y) :=
    (e.toLinearMap.compLeft G).comp ((Submodule.subtype _).comp E.toLinearMap)
  have hLa : ∀ x t, L x t = e ((E x).1 t) := fun _ _ => rfl
  have hact : ∀ g c x t, L (extTensor (smInd P ρ) m (g, c) x) t = y (1, c) (L x (t * g)) := by
    intro g c x t
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h1 : extTensor (smInd P ρ) m (g, c) (a ⊗ₜ[ℂ] b) = smInd P ρ g a ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      have h2 : extTensor ρ m (1, c) (a.1.1 (t * g) ⊗ₜ[ℂ] b) = a.1.1 (t * g) ⊗ₜ[ℂ] m c b := by
        simp [extTensor]
      rw [h1, hLa, hLa, hE, hE, ← he, h2]
      rfl
    | add x x' hx hx' => simp only [map_add (f := _), Pi.add_apply, hx, hx']
  have hsurj : ∀ z ∈ IndF P.subtype (y.comp (MonoidHom.inl P Γ)) ⊤, ∃ x, L x = z := by
    intro z hz
    have hlaw : ∀ (p : P) g, z (p * g) = y (p, 1) (z g) := hz.1.2
    have hz' : (fun g => e.symm (z g)) ∈ IndF P.subtype ((extTensor ρ m).comp (MonoidHom.inl P Γ)) ⊤ := by
      refine ⟨⟨fun _ => trivial, fun p g => ?_⟩, ?_⟩
      · apply e.injective
        show e (e.symm (z (p * g))) = e (extTensor ρ m (p, 1) (e.symm (z g)))
        rw [he, e.apply_symm_apply, e.apply_symm_apply, hlaw]
      · refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds hz.2 (by simp)) fun u hu => ?_)
        funext x
        have h2 : z (x * u) = z x := congrFun hu x
        show e.symm (z (x * u)) = e.symm (z x)
        rw [h2]
    refine ⟨E.symm ⟨_, hz'⟩, funext fun t => ?_⟩
    rw [hLa, E.apply_symm_apply]
    exact e.apply_symm_apply _
  intro Q hQ hG hΓ
  let Q' : Subrepresentation (extTensor (smInd P ρ) m) :=
    ⟨Q.comap L, by
      rintro ⟨g, c⟩ x hx
      have h1 := hΓ c _ (hG g _ hx)
      have h2 : L (extTensor (smInd P ρ) m (g, c) x) = fun t => y (1, c) (L x (t * g)) := funext (hact g c x)
      show L _ ∈ Q
      rw [h2]
      exact h1⟩
  rcases hirr.eq_bot_or_eq_top Q' with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun q hq => ?_
    obtain ⟨x, rfl⟩ := hsurj q (hQ hq)
    have hx : x ∈ Q'.toSubmodule := hq
    rw [h] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  · right
    refine le_antisymm hQ fun z hz => ?_
    obtain ⟨x, rfl⟩ := hsurj z hz
    have hx : x ∈ Q'.toSubmodule := by rw [h]; trivial
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private def cj {G : Type} [Group G] (c : G) (U : Subgroup G) : Subgroup G where
  carrier := {x | c⁻¹ * x * c ∈ U}
  one_mem' := by simp [U.one_mem]
  mul_mem' {a b} ha hb := by
    have h := U.mul_mem ha hb
    have e : c⁻¹ * (a * b) * c = c⁻¹ * a * c * (c⁻¹ * b * c) := by group
    simpa only [Set.mem_setOf_eq, e] using h
  inv_mem' {a} ha := by
    have h := U.inv_mem ha
    have e : c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ := by group
    simpa only [Set.mem_setOf_eq, e] using h

private theorem mem_cj {G : Type} [Group G] {c x : G} {U : Subgroup G} : x ∈ cj c U ↔ c⁻¹ * x * c ∈ U := Iff.rfl

private theorem isOpen_cj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) : IsOpen (cj c U : Set G) :=
  hU.preimage (f := fun x => c⁻¹ * x * c) ((continuous_const.mul continuous_id).mul continuous_const)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (S : Finset (Pl K)), (∀ U, Lev U → CO (levOn (n := n) S U) ∧ levOn S U ≤ AdelicGLn.integralFiniteGL K n) ∧
      (∀ U U' : ∀ v : Pl K, Subgroup (Gw n v), Lev U → Lev U' → Lev (fun v => U v ⊓ U' v) ∧ levOn S (fun v => U v ⊓ U' v) = levOn S U ⊓ levOn S U') ∧
      (∀ (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧ Continuous (arc1 : archCompact K n → G1 K n) ∧ CompactSpace (archCompact K n) ∧
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n), Function.Injective w → IsEmb w ι → S = im w → ∀ U, Lev U → ∀ g,
        ∃ U', Lev U' ∧ ∀ u ∈ levOn S U', (ι g)⁻¹ * u * ι g ∈ levOn S U := by
  intro K _ _ n S
  have hmem : ∀ (U : ∀ v : Pl K, Subgroup (Gw n v)) (u : FA K n), u ∈ levOn S U ↔ ∀ v, finAt v (finEmb K n u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n) := fun _ _ => Iff.rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨ho, hc, hi, -⟩ := UpperTheory.levF_isOpen_isCompact_le_integral K n
      (fun v => if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) n) S
      (fun v hv => by simpa only [if_pos hv] using And.intro (hU v).1.2 (hU v).2) (fun v hv => if_neg hv)
    exact ⟨⟨hc, ho⟩, hi⟩
  · intro U U' hU hU'
    refine ⟨fun v => ⟨⟨(hU v).1.1.inter_right (Subgroup.isClosed_of_isOpen _ (hU' v).1.2),
      (hU v).1.2.inter (hU' v).1.2⟩, inf_le_left.trans (hU v).2⟩, ?_⟩
    ext u
    rw [Subgroup.mem_inf, hmem, hmem, hmem]
    constructor
    · intro h
      refine ⟨fun v => ?_, fun v => ?_⟩
      · have h' := h v
        by_cases hv : v ∈ S
        · rw [if_pos hv] at h' ⊢
          exact (Subgroup.mem_inf.1 h').1
        · rw [if_neg hv] at h' ⊢
          exact h'
      · have h' := h v
        by_cases hv : v ∈ S
        · rw [if_pos hv] at h' ⊢
          exact (Subgroup.mem_inf.1 h').2
        · rw [if_neg hv] at h' ⊢
          exact h'
    · rintro ⟨h₁, h₂⟩ v
      have a := h₁ v
      have b := h₂ v
      by_cases hv : v ∈ S
      · rw [if_pos hv] at a b ⊢
        exact Subgroup.mem_inf.2 ⟨a, b⟩
      · rw [if_neg hv] at a b ⊢
        exact a
  · intro k h
    exact (MultiplicityOne.finProj_mul_archProj_comm h _).symm
  · exact continuous_archP.comp continuous_subtype_val
  · have hcl : IsClosed (archCompact K n : Set (archGroup K n)) :=
      (isCompact_maxCompact (K := K) (n := n)).isClosed.preimage continuous_infEmb
    have hg : Continuous fun z : AdelicGLn.AdelicGL K n => archEquiv K n (AdelicGLn.prodEquiv K n z).1 :=
      (archEquiv K n).continuous.comp (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous)
    refine isCompact_iff_compactSpace.1 (((isCompact_maxCompact (K := K) (n := n)).image hg).of_isClosed_subset hcl ?_)
    intro x hx
    exact ⟨infEmb K n x, hx, by simp [prodEquiv_infEmb]⟩
  · intro r w ι hinj hι hS U hU g
    obtain ⟨-, -, hout, -⟩ := (embEx n w hinj).2 ι hι
    refine ⟨fun v => U v ⊓ cj (GM.cf v (ι g)) (U v), fun v => ?_, fun u hu => ?_⟩
    · have ho := isOpen_cj (GM.cf v (ι g)) (hU v).1.2
      exact ⟨⟨(hU v).1.1.inter_right (Subgroup.isClosed_of_isOpen _ ho), (hU v).1.2.inter ho⟩,
        inf_le_left.trans (hU v).2⟩
    · refine (hmem _ _).2 fun v => ?_
      have hcf : finAt v (finEmb K n ((ι g)⁻¹ * u * ι g)) =
          (GM.cf v (ι g))⁻¹ * finAt v (finEmb K n u) * GM.cf v (ι g) := by
        simp only [map_mul, map_inv, finAt_mul, finAt_inv, GM.cf]
      have hu' := (hmem _ _).1 hu v
      rw [hcf]
      by_cases hv : v ∈ S
      · rw [if_pos hv] at hu' ⊢
        exact mem_cj.1 (Subgroup.mem_inf.1 hu').2
      · rw [if_neg hv] at hu' ⊢
        rw [hout g v (hS ▸ hv)]
        simpa using hu'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LocDat
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem irr_twist {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (f : G →* H) (hf : Function.Surjective f) (χ : G →* ℂˣ) (hi : ρ.IsIrreducible) (hs : Schur ρ) :
    (twist (ρ.comp f) χ).IsIrreducible ∧ Schur (twist (ρ.comp f) χ) := by
  constructor
  · let E : Subrepresentation (twist (ρ.comp f) χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun h v hv => by
          obtain ⟨g, rfl⟩ := hf h
          have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rw [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1
          exact h1⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          rw [twist_apply]
          exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule (f g) hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact E.isSimpleOrder_iff.2 hi
  · intro T hT
    refine hs T fun h v => ?_
    obtain ⟨g, rfl⟩ := hf h
    have h1 := hT g v
    rw [twist_apply, twist_apply, map_smul] at h1
    exact smul_right_injective V (χ g).ne_zero h1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.locDat :
    ∀ {K : Type} [Field K] [NumberField K] (w : Pl K) (σ₁ σ₂ : SmIrr (Gw 2 w)), IsUnitarisable σ₁.ρ → IsUnitarisable σ₂.ρ → LocOk (PW w) (rhoW w σ₁ σ₂) := by
  intro K _ _ w σ₁ σ₂ u₁ u₂
  have hT := tensSimple σ₁.ρ σ₂.ρ σ₁.irred (schurSm 2 w σ₁.ρ σ₁.smooth σ₁.irred) σ₂.irred
  have hsurj : Function.Surjective (lev₂ w) := by
    intro g
    refine ⟨⟨leviEmb _ _ (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) g), leviEmb_mem_parab _ _ _⟩, ?_⟩
    change (leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).symm (leviProj _ _ _) = g
    rw [leviProj_leviEmb, MulEquiv.symm_apply_apply]
  have hR := irr_twist _ (lev₂ w) hsurj (dl w) hT.1 (hT.2 (schurSm 2 w σ₂.ρ σ₂.smooth σ₂.irred))
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hI : (smInd (PW w) (rhoW w σ₁ σ₂)).IsIrreducible :=
    UpperTheory.Lit.Mix.twoAt_charZero (w.adicCompletion K) 2 2 _ _ σ₁.ρ σ₂.ρ σ₁.smooth σ₁.irred u₁ σ₂.smooth σ₂.irred u₂
  refine ⟨⟨_, ⟨GlobalTheory.SplitFlip.isCompact_KO, GlobalTheory.SplitFlip.isOpen_KO⟩, fun g => ?_⟩, fun N hN => ?_, hR.1, hR.2, hI,
    schurSm (2 + 2) w _ (isSmooth_smoothRep _) hI⟩
  · obtain ⟨p, k, hk, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (two (stdSum (rfl : 2 + 2 = 2 + 2))) g
    exact ⟨p, p.2, k, hk, e⟩
  · obtain ⟨U, h1, -, h2⟩ := GlobalTheory.LocalThetaGL.compact_open_basis (k := w.adicCompletion K) (Fin (2 + 2)) N hN
    exact ⟨U, h1, h2⟩
end

