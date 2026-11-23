module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.SelLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LiftOfBar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.BoxUnit
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)}

private theorem adicCont_comp_ringHom_of_map_le {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (hIJ : I.map f ≤ J) {a : Γ → R} (ha : AdicCont I a) :
    AdicCont J (fun g => f (a g)) := by
  intro N
  have h : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ N
  have := (ha N).comp (Ideal.quotientMap (J ^ N) f h)
  convert this using 1
  funext g
  simp [Ideal.quotientMap_mk]

private theorem lift_pt (S : Space O F 3) (ξ : S.R →ₐ[O] O) : UpperTheory.V.Fr.IsLift O (S.ρ.map (ξ : S.R →+* O)) := by
  have hres : (res O O : O →+* ResidueField O).comp (ξ : S.R →+* O) = (res O S.R : S.R →+* ResidueField O) :=
    RingHom.ext fun x => res_map ξ x
  have hm : (maximalIdeal S.R).map (ξ : S.R →+* O) ≤ maximalIdeal O := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O O]
    have := (res_eq_zero_iff O S.R x).2 hx
    simpa [res_map] using this
  obtain ⟨hc, hb, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.1 i j)
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

private theorem box_pt {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3) (ξ : S.R →ₐ[O] O) :
    ∃ B : Box F 3 O, B.Of (S.ρ.map (ξ : S.R →+* O)) ∧ B.Cont (maximalIdeal O) := by
  have e : NRep.map ((ξ : S.R →+* O).comp (S.A.val : S.A →+* S.R)) S.u = S.ρ.map (ξ : S.R →+* O) := by
    apply NRep.ext
    · rfl
    · funext v i
      ext g
      rfl
  refine pr_box hF O (maximalIdeal O) _ (lift_pt S ξ).1 fun v => ?_
  rw [← e]
  exact flag hF (Or.inr rfl) S O _ v

private theorem box_unit [Algebra ℤ_[l] O] {ρ : NRep F 3 O} {B₀ : Box F 3 O} (h : B₀.Of ρ)
    (hc : B₀.Cont (maximalIdeal O)) (v : F.V) (i : Fin 2) (hu : UnitAt ρ v i) :
    ∃ B : Box F 3 O, B.Of ρ ∧ B.Cont (maximalIdeal O) ∧
      UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i := by
  classical
  obtain ⟨g, t, ht, hup, hdiag, hstep⟩ := hu
  have hr : ∀ s : F.Gv v, (B₀.r ((F.loc v) s)).mat = ρ.r ((F.loc0 v) s) := fun s => h.res ((F.loc0 v) s)
  let B : Box F 3 O :=
    { r := B₀.r
      nu := B₀.nu
      g := Function.update B₀.g v g
      tri := by
        intro w s
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self, hr s, ← ht s]
          exact hup s
        · rw [Function.update_of_ne hw]
          exact B₀.tri w s }
  have hBg : B.g v = g := by
    show Function.update B₀.g v g v = g
    exact Function.update_self _ _ _
  have hBw : ∀ w, w ≠ v → B.g w = B₀.g w := fun w hw => by
    show Function.update B₀.g v g w = B₀.g w
    exact Function.update_of_ne hw _ _
  have htri : triOf B v = t := by
    ext s : 1
    apply Units.ext
    show (B.g v : Matrix (Fin 3) (Fin 3) O) * (B₀.r ((F.loc v) s)).mat * ((B.g v)⁻¹ : GL (Fin 3) O) = _
    rw [hBg, hr s, ht s]
  refine ⟨B, ⟨h.atc, h.res, fun w j s => ?_⟩, hc, ?_⟩
  · by_cases hw : w = v
    · subst hw
      show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBg, ← ht s]
      exact hdiag s j
    · show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBw w hw]
      exact h.psi w j s
  · rw [htri]
    exact hstep

private theorem zn_ext {C₀ : ℕ} (hF : F.Ok C₀) (B : Box F 3 O) (k : ℕ) {z z' : F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)}
    (hz : z ∈ ZN B k) (hz' : z' ∈ ZN B k)
    (h : ∀ s : F.G0, z s * ((boxK B k).r s).mat = z' s * ((boxK B k).r s).mat) : z = z' := by
  have hG : ∀ s : F.G0, z s = z' s := by
    intro s
    have hu : ((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 :=
      Units.mul_inv _
    calc z s = z s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [hu, mul_one]
      _ = z' s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [← mul_assoc, h s, mul_assoc]
      _ = z' s := by rw [hu, mul_one]
  funext s
  have hc : ∀ y ∈ ZN B k, y (s * F.c) = y s := fun y hy => by
    rw [hy.1.1.2 s F.c, hy.2.1, map_zero, add_zero]
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact hG ⟨s, MonoidHom.mem_ker.mpr hs⟩
  · have hsc : F.del (s * F.c) = 1 := by
      rw [map_mul, hs, hF.del_c]
      rfl
    rw [← hc z hz, ← hc z' hz']
    exact hG ⟨s * F.c, MonoidHom.mem_ker.mpr hsc⟩

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.tan :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (v : F.V) (i : Fin 2), UnitAt (S.ρ.map (ξ : S.R →+* O)) v i → ∃ δ ∈ WDer S.ρ ξ O, ∃ δ' ∈ WDer S.ρ ξ O, LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ F C₀ hF hl cw hcw hGWL hL S ξ v i hu
  obtain ⟨B₀, hB₀, hc₀⟩ := box_pt hF S ξ
  obtain ⟨B, hB, hc, hstep⟩ := box_unit hB₀ hc₀ v i hu
  obtain ⟨C, hC⟩ := selLow l O F C₀ hF hl _ B (lift_pt S ξ) hB hc cw hcw hGWL hL v i hstep
  let T : Set S.R := {a | ∃ (w : F.V) (j : Fin 3) (s : F.Gv w), s ∈ F.Iv w ∧ a = ((S.ρ.ψ w j s : S.Rˣ) : S.R)}
  obtain ⟨δ, δ', hd, hdT, hd', hdT', hli⟩ := rankTwo l O S.R ξ T C hl (by
    intro k hk X hX hXf
    classical
    refine (hC k hk).2.trans (Nat.mul_le_mul_left C ?_)
    have hex : ∀ z ∈ ZN B k, ∃ δ ∈ X,
        ∀ (s : F.G0) (a b : Fin 3), δ (S.ρ.r s a b) = (z s * ((boxK B k).r s).mat) a b := by
      intro z hz
      obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := derOf l O F C₀ hF hl S ξ B hB hc k hk z hz
      refine ⟨δ, ?_, h3⟩
      rw [hX]
      refine ⟨h1, ?_⟩
      rintro a ⟨w, j, s, hs, rfl⟩
      exact h2 w j s hs
    let f : (F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)) → (S.R →ₗ[O] Ok l O k) := fun z =>
      if hz : z ∈ ZN B k then (hex z hz).choose else 0
    refine Set.ncard_le_ncard_of_injOn f (fun z hz => ?_) (fun z hz z' hz' he => ?_) hXf
    · simp only [f, dif_pos hz]
      exact (hex z hz).choose_spec.1
    · apply zn_ext hF B k hz hz'
      intro s
      ext a b
      have h1 := (hex z hz).choose_spec.2 s a b
      have h2 := (hex z' hz').choose_spec.2 s a b
      simp only [f, dif_pos hz, dif_pos hz'] at he
      rw [← h1, ← h2, he])
  exact ⟨δ, ⟨hd, fun w j s hs => hdT _ ⟨w, j, s, hs, rfl⟩⟩, δ', ⟨hd', fun w j s hs => hdT' _ ⟨w, j, s, hs, rfl⟩⟩, hli⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CupUnr
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V UpperTheory.V.Loc
open TensorProduct Module

private theorem exists_deg (l : ℕ) [Fact l.Prime] :
    ∃ (d : GQ l → ℚ_[l]) (σ : GQ l), Continuous d ∧ (∀ s s', d (s * s') = d s + d s') ∧
      (∀ s ∈ Iq l, d s = 0) ∧ ∀ n : ℕ, 0 < n → d (σ ^ n) ≠ 0 := by
  obtain ⟨σ, hσ, -⟩ := frobCyc l
  obtain ⟨f, hf, hI, h1⟩ := frobFree σ hσ (Multiplicative ℤ_[l]) (Multiplicative.ofAdd 1)
  refine ⟨fun s => ((Multiplicative.toAdd (f s) : ℤ_[l]) : ℚ_[l]), σ, ?_, fun s s' => by simp, fun s hs => ?_,
    fun n hn => ?_⟩
  · exact continuous_subtype_val.comp (continuous_toAdd.comp hf)
  · simp [hI s hs]
  · simp [h1, hn.ne']

section

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]

omit [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
private theorem cyc_val (K : FinExt l) (g : ↥(GK K)) :
    (cycA l l E (g : GQ l) : E) = algebraMap ℚ_[l] E (cycLL ((PP l).PD K) ℚ_[l] g : ℚ_[l]) := by
  change algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E (((PP l).PD K).χ g : ℚ_[l])
  rw [(PP l).PD_χ, (cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
  rfl

omit [FiniteDimensional ℚ_[l] E] in
private theorem cyc_cont [IsTopologicalRing E] : Continuous fun g : GQ l => (cycA l l E g : E) := by
  have h1 : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val
  exact h1.comp (Units.continuous_val.comp (cycFacts l l).1)

private theorem gk_case [IsTopologicalRing E] (hP : LocalPublishedTheorems) (K : FinExt l) (κ : ↥(GK K) → E)
    (hκ : κ ∈ UpperTheory.V.Loc.finiteCocycles (GK K).subtype (chRep ((cycA l l E).comp (GK K).subtype)))
    (d : ↥(GK K) → ℚ_[l]) (hd : Continuous d) (hadd : ∀ s s', d (s * s') = d s + d s')
    (hI : ∀ s : ↥(GK K), (s : GQ l) ∈ Iq l → d s = 0) :
    ∃ β : ↥(GK K) → E, Continuous β ∧
      ∀ s s', β (s * s') = β s + (cycA l l E (s : GQ l) : E) * β s' - d s' • κ s := by
  classical
  haveI : ContinuousSMul ℚ_[l] E := IsModuleTopology.toContinuousSMul ℚ_[l] E
  haveI := K.2
  have hφ : IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  obtain ⟨T⟩ := tiedP l
  have hc : Continuous fun g : ↥(GK K) => (((cycA l l E).comp (GK K).subtype) g : E) :=
    cyc_cont.comp continuous_subtype_val
  have hdR : IsDR ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype))) :=
    (isCrIff K _).2.1 (charFil _ hφ _ hc 1 ⟨⊤, isOpen_univ, fun g _ _ => (zpow_one _).symm⟩).1
  have hρ : ∀ g x, resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)) g x =
      (cycLL ((PP l).PD K) ℚ_[l] g : ℚ_[l]) • x := fun g x => by
    rw [Algebra.smul_def, ← cyc_val]
    rfl
  let b := Module.finBasis ℚ_[l] E
  have hdual : IsDual1 ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)))
      (1 : Representation ℚ_[l] ↥(GK K) E) b.toDual := by
    refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
    · rw [hρ]
      simp
    · exact b.toDual_inj x (LinearMap.ext hx)
    · exact b.ext_elem fun i => by rw [← b.toDual_apply_right, hy, map_zero, Finsupp.zero_apply]
  have hκ' : κ ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype))) := by
    rw [← (isCrField K _).2.2]
    exact hκ
  have hD := ((hP.bk l (PP l) (AIP l) T K).2.1 E E _ 1 b.toDual
    (fun x => hc.mul continuous_const) (fun y => continuous_const) hdR hdual).1 κ hκ'.1
  have hf : ∀ i, ∃ f : ↥(GK K) → ℚ_[l], Continuous f ∧ ∀ s s', f (s * s') =
      f s + (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - d s' * b.repr (κ s) i := by
    intro i
    have hz : (fun s => d s • b i) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (1 : Representation ℚ_[l] ↥(GK K) E) := by
      rw [← (isCrField K _).2.2]
      refine (z1fUnr hP _ hφ (1 : Representation ℚ_[l] ↥(GK K) E) continuous_snd (fun _ _ => rfl) _
        ⟨hd.smul continuous_const, fun s s' => ?_⟩).2 fun s hs => ?_
      · simp [hadd, add_smul]
      · simp [hI s hs]
    obtain ⟨f, hf, h⟩ := hD.1 hκ' _ hz
    refine ⟨f, hf, fun s s' => ?_⟩
    have h1 : (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - f (s * s') + f s =
      b.toDual (κ s) (d s' • b i) := congrFun h (s, s')
    rw [map_smul, b.toDual_apply_left, smul_eq_mul] at h1
    linear_combination -h1
  choose f hf hff using hf
  refine ⟨fun s => ∑ i, f i s • b i, continuous_finsetSum _ fun i _ => (hf i).smul continuous_const,
    fun s s' => ?_⟩
  rw [cyc_val, ← Algebra.smul_def]
  conv_rhs => rw [← b.sum_repr (κ s)]
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← add_smul,
    ← sub_smul, hff]

end

theorem UpperTheory.V.Z.J.cupUnr :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l), IsOpenEmbedding φ → ∀ {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ κ ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ((cycA l l E).comp φ)), ∃ u β : G → E, Continuous u ∧ Continuous β ∧ (∀ s s', u (s * s') = u s + u s') ∧ (∀ s, φ s ∈ Iq l → u s = 0) ∧ (∃ s, u s ≠ 0) ∧ ∀ s s', β (s * s') = β s + (cycA l l E (φ s) : E) * β s' - κ s * u s' := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨d, σ, hd, hadd, hI, hσ⟩ := exists_deg l
  have hφ1 : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun hφe g
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by rw [← hφ1, e.apply_symm_apply]
  obtain ⟨⟨hκ1, hκ2⟩, x, hx⟩ := hκ
  obtain ⟨β, hβ, hβ'⟩ := gk_case hP K (κ ∘ e.symm) ⟨⟨hκ1.comp he', fun g h => by
      have := hκ2 (e.symm g) (e.symm h)
      rw [← map_mul] at this
      refine this.trans ?_
      change _ + (cycA l l E (φ (e.symm g)) : E) * _ = _
      rw [hφ']
      rfl⟩, x, fun g => by
      refine (hx (e.symm g)).trans ?_
      congr 2
      unfold actC
      rw [hφ']
      congr 1
      refine LinearMap.ext fun y => ?_
      change (cycA l l E (φ (e.symm g)) : E) * _ = _
      rw [hφ']
      rfl⟩ (fun g => d g) (hd.comp continuous_subtype_val) (fun s s' => hadd _ _) (fun s hs => hI _ hs)
  refine ⟨fun s => algebraMap ℚ_[l] E (d (φ s)), β ∘ e,
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp (hd.comp hφ.continuous),
    hβ.comp he, fun s s' => by simp [hadd], fun s hs => by simp [hI _ hs], ?_, fun s s' => ?_⟩
  · haveI := K.2
    obtain ⟨n, hn, -, s, hs⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := φ.range)
      (by rw [hind]; exact Module.finrank_pos.ne') σ
    exact ⟨s, by simpa [hs] using hσ n hn⟩
  · have := hβ' (e s) (e s')
    simp only [hφ1, Function.comp_apply, MulEquiv.symm_apply_apply, ← map_mul] at this
    rw [Function.comp_apply, this, Algebra.smul_def, mul_comm (κ s)]
    rfl
end

