module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemOfUnder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0052
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0050
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResidualCharpolyRankFour
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0051
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfUnder
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem val_iff {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (M : ℕ) : A.valuation (M : Ω) < 1 ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  change ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ w.asIdeal at h
  simpa only [map_natCast, Int.cast_natCast] using h (M : 𝓞 L)
private theorem mem_of_under {L : Type} [Field L] [NumberField L] [IsCMField L] {w w' : Plc L}
    (e : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (M : ℕ) : (M : 𝓞 L) ∈ w'.asIdeal ↔ (M : 𝓞 L) ∈ w.asIdeal := by
  have hl : ∀ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal ↔ (M : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  rw [hl, hl, e]
private theorem core (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hl : l ≠ 2) (M m : ℕ) (hM : M ≠ 0) (h2 : 2 * l ∣ M) (hU : UnrSplit L M)
    (r : G L Ω →* GL (Fin 2) (Qbar l)) (hr : AdInW ι M m r) (w₀ : Plc L) (hw₀ : (M : 𝓞 L) ∈ w₀.asIdeal) :
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧
      (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B) ∧ ∀ τ, π.IsLocComp w₀ τ → PT τ := by
  have hlM : l ∣ M := (Dvd.intro_left 2 rfl).trans h2
  have h2M : 2 ∣ M := (Dvd.intro l rfl).trans h2
  have hdv : ∀ {a : ℕ} {w : Plc L}, a ∣ M → (a : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := by
    rintro a w ⟨b, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨σ, HT, hσ, hg, hpt, hunr, hwt⟩ := _root_.UpperTheory.V.Z.Sym.W.aboveWeight P L Ω l ι hl M m hM hlM hU r hr
  obtain ⟨S, hS, h0S, hSi, hSm⟩ := selectW L {w | (M : 𝓞 L) ∈ w.asIdeal} w₀ hw₀
  obtain ⟨Q, hQ, hQi, hQm⟩ := Ga.select L {w | IsSplitAt w ∧ (M : 𝓞 L) ∉ w.asIdeal ∧ ∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r}
  have hfin : S.Finite := by
    have h0 : Ideal.span {(M : 𝓞 L)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (hS hv)
  have key : ∀ w : Plc L, ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (w ∈ S ∪ Q → CompEq σ w ψ) ∧ (w ∈ S → NoLk (ψ 0 / ψ 1)) ∧
      (w ∈ Q → (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)) := fun w => by
    by_cases hq : w ∈ Q
    · obtain ⟨h1, h3, h4⟩ := hQ hq
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      obtain ⟨ψ, a1, a2, a3, a4⟩ := _root_.UpperTheory.V.Z.Sym.W.good_w_statement P.af L Ω l ι r w (mt (hdv hlM) h3)
        (fun A hA => hr.unr A (mt (val_iff hA M).1 h3)) h4 τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
      exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun h => absurd (hS h) h3, fun _ => ⟨a3, a4⟩⟩
    by_cases hs : w ∈ S
    · have h1 := hU.split w (hS hs)
      obtain ⟨τ, hτ⟩ := hg.comp w h1
      by_cases hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
        obtain ⟨⟨ψ, a1, a2, a3⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.above_w_statement P.af L Ω l ι hl r hr.cont m hr.gap w hw HT (hpt w h1 τ hτ).2 A hA
          (hr.above A ((val_iff hA l).2 hw)) τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
      · obtain ⟨ψ, a1, a2, a3⟩ := _root_.UpperTheory.V.Z.Sym.W.away_w_statement P.af L Ω l ι r hr.cont hr.unl w hw τ (hg.loc w h1 τ hτ) (hpt w h1 τ hτ).1
        exact ⟨ψ, fun _ => ⟨a1, τ, hτ, a2⟩, fun _ => a3, fun h => absurd h hq⟩
    · exact ⟨1, fun h => (h.elim hs hq).elim, fun h => absurd h hs, fun h => absurd h hq⟩
  choose ψ hψ hnl hψ' using key
  have hgood : Ga.GoodSet ι M r σ Q ψ :=
    ⟨fun w hw => ⟨(hQ hw).1, mt (hdv hlM) (hQ hw).2.1, hψ w (Or.inr hw)⟩, fun w a b c => hQm w ⟨a, b, c⟩⟩
  have hgap := hr.gap
  have := hA L hU.unr hfin.toFinset Q ?_ ?_ ?_ σ hσ (m - 1) (by omega) hwt ?_ ψ ?_ hψ'
  · rcases this with ⟨σ₃, h1, hu, h4, h3⟩ | ⟨σ', h1, h3⟩
    · obtain ⟨π, a, b, c, d⟩ := _root_.UpperTheory.V.Z.Sym.W.branch1W_alt P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ₃ h1 h3
      exact ⟨π, a, b, c, fun w hw => d.unr w (hu w fun w' hw' e => hw ((mem_of_under e M).1 (hS (hfin.mem_toFinset.1 hw')))),
        _root_.UpperTheory.V.Z.Sym.W.plain_at_w_statement P.af.litN L σ₃ π h1 d w₀ (hU.split w₀ hw₀) _ (hnl w₀ h0S) (h4 w₀ (hfin.mem_toFinset.2 h0S))⟩
    · exact (_root_.UpperTheory.V.Z.Sym.W.branch_two_w_statement P L Ω l ι hl hU.unr M m hM r σ hr hg Q ψ hgood (fun w hw => (hψ' w hw).2) σ' h1 h3).elim
  · rw [hfin.coe_toFinset, Set.disjoint_left]
    exact fun w a b => (hQ b).2.1 (hS a)
  · rw [hfin.coe_toFinset]
    refine ⟨fun w hw => hw.elim (fun h => hU.split w (hS h)) fun h => (hQ h).1, ?_⟩
    rintro a (ha | ha) b (hb | hb) e
    · exact hSi ha hb e
    · exact absurd ((mem_of_under e M).1 (hS ha)) (hQ hb).2.1
    · exact absurd ((mem_of_under e M).2 (hS hb)) (hQ ha).2.1
    · exact hQi ha hb e
  · intro w hw
    obtain ⟨w', a, b⟩ := hSm w (hdv h2M (by exact_mod_cast hw))
    exact ⟨w', hfin.mem_toFinset.2 a, b⟩
  · intro w hw
    refine hunr w fun h => ?_
    obtain ⟨w', a, b⟩ := hSm w h
    exact hw w' (hfin.mem_toFinset.2 a) b
  · rw [hfin.coe_toFinset]
    exact hψ
theorem adjoint_automorphy_w_of_pure_weight_adjoint_lift (P : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility) (hA : AdLiftW) : AdAutW := by
  intro L Ω _ _ _ _ _ _ l _ ι hl M m hM h2 hU r hr
  obtain ⟨w₁, hw₁⟩ : ∃ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal := by
    have hl1 : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf (IsAlgClosed.lift (R := ℚ) (M := Qbar l) (S := L)).toRingHom).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨b, rfl⟩ := (Dvd.intro_left 2 rfl).trans h2
    exact ⟨_, by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hl1⟩
  obtain ⟨π, a, b, c, d, -⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w₁ hw₁
  refine ⟨⟨π, a, b, c⟩, glueW L Ω l ι _ fun w => ?_⟩
  by_cases hw : (M : 𝓞 L) ∈ w.asIdeal
  · obtain ⟨π', -, -, c', -, e⟩ := core P hA L Ω l ι hl M m hM h2 hU r hr w hw
    exact ⟨π', c', Or.inr e⟩
  · exact ⟨π, c, Or.inl (d w hw)⟩
end UpperTheory.V.Z.Sym.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigidEndTwoWOfPrintedAdjointLifting
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.rigid_end_two_w_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.GalN.V.RigidityEndomorphismWeightTwo := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨσ hF A _ _ r hr hII h11 K _ _ _ _ hK2 hK W hWc hW hdet haut hWit hfree θ hθ R hR
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := Db.algClo L Ω
  haveI := Db.algClo K Ω
  obtain ⟨-, ka, hka, hrig⟩ := _root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed
  have hof := UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r
  generalize Chr.Psi l e (Chr.dirG ℚ Ω ψ) = Ψ at *
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmk := Pr.marks_of_link k hok hl hσ hΨσ
  have hLη := Db.galL_le k
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hK ▸ hLη)
  obtain ⟨_, hsol⟩ := Db.galKL K L k.ab
  haveI := Db.locHom c A
  haveI := (isNoetherianRing_iff_ideal_fg A).2 fun I => (IsPrincipalIdealRing.principal I).fg
  haveI : Normal ℚ L := k.ab.toIsGalois.to_normal
  have hb : U3.Block η r := fun g hg a b hab => Subtype.ext (hII.1 g hg a b hab)
  have hg₂ : g₂ ∈ η.ker := hmk.ηg
  have hgs : U3.gstar σ g₂ ∈ η.ker := by
    show η (σ * g₂⁻¹ * σ) = 1
    rw [map_mul, map_mul, map_inv, hmk.ηg, hmk.ηc]
    simp
  have hr' : Pr.OrdPt l η Ψ σ g₂ B r :=
    ⟨hr.red, hr.cont, ⟨hr.norm.atc,
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero],
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero]⟩, hr.away, hr.ord⟩
  have hFl : Flagged (W.comp (Base.galEmb ℚ K Ω)) := Dn.flagAll_of K Ω l 2 _ fun w hw =>
    let ⟨A', a1, κ, a2⟩ := hof hr' hb h11 K hK _ (fun s => hW _ (hK.ge (Base.galEmb_mem ℚ K Ω s))) w hw
    ⟨A', a1, κ, a2.choose_spec.2.1⟩
  obtain ⟨ρ', h1, h2, h3⟩ := Pr.exists_nrep2 k hok hl hσ r hr' hb
  have hηL : ∀ s : G L Ω, η (Base.galEmb ℚ L Ω s) = 1 := fun s => hLη (Base.galEmb_mem ℚ L Ω s)
  have hηK : ∀ s : G K Ω, η (Base.galEmb ℚ K Ω s) = 1 := fun s => hK.ge (Base.galEmb_mem ℚ K Ω s)
  let χ : G ℚ Ω →* (ResidueField A)ˣ := (Units.map ((residue A).comp (algebraMap c.O A)).toMonoidHom).comp Ψ
  have hU : U3.MatIrr ((Base.galOf ℚ L Ω).subgroupOf η.ker) (Pr.gm (W.comp η.ker.subtype)) := by
    have irr2 {G κ k A : Type} [Group G] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
        (r : G →* GL (Fin 2) κ) (hr : U3.MatIrr ⊤ (Pr.gm r)) (j : A →+* κ) (hj : Function.Injective j) (φ : A →+* k)
        (χ : G →* kˣ) (t : G → A) (ht : ∀ g, j (t g) = (Pr.gm r g).trace)
        (hχ : ∀ g, φ (t g) = (χ g : kˣ) + ((χ g)⁻¹ : kˣ)) (U : Subgroup G) [U.Normal] {u : G} (hu : u ∈ U)
        (hd : (Pr.gm r u).det = 1) (hne : χ u ^ 2 ≠ 1) : U3.MatIrr U (Pr.gm r) := by
      have hy : ((χ u : kˣ) : k) ^ 2 - 1 ≠ 0 := fun h => hne (Units.ext (by simpa [sub_eq_zero] using h))
      rcases Pr.cliffPrime G κ 2 Nat.prime_two r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
      · exact h
      · exfalso
        obtain ⟨a, ha⟩ := h u hu
        have e : t u ^ 2 = 4 := by
          apply hj
          rw [map_pow, ht, map_ofNat]
          rw [ha] at hd ⊢
          simp only [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at hd ⊢
          push_cast
          linear_combination 4 * hd
        have e2 := congrArg φ e
        rw [map_pow, hχ, map_ofNat] at e2
        have e3 := (χ u).mul_inv
        apply pow_ne_zero 2 hy
        linear_combination ((χ u : kˣ) : k) ^ 2 * e2 - (2 * ((χ u : kˣ) : k) ^ 2 + (χ u : kˣ) * ((χ u)⁻¹ : kˣ) + 1) * e3
      · exfalso
        obtain ⟨g, hg⟩ := htr 0 1
        have hne' : ∀ i, π g i ≠ i := by
          intro i hi
          fin_cases i
          · exact absurd (hg.symm.trans hi) (by decide)
          · exact absurd ((π g).injective (hg.trans hi.symm)) (by decide)
        have tr0 : ∀ s ∈ U, (Pr.gm r (g * s)).trace = 0 := fun s hs => by
          rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace κ b]
          refine Finset.sum_eq_zero fun i _ => ?_
          obtain ⟨a, ha⟩ := hπ g i
          have := hla i ⟨s, hs⟩
          simp only [Pr.gm] at this ha
          rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
          simp only [Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
          rw [this, Matrix.mulVec_smul, ha]
          simp [hne' i]
        have z : ∀ s ∈ U, ((χ (g * s) : kˣ) : k) ^ 2 + 1 = 0 := fun s hs => by
          have e : t (g * s) = 0 := hj (by rw [ht, tr0 s hs, map_zero])
          have e2 := hχ (g * s)
          rw [e, map_zero] at e2
          have e3 := (χ (g * s)).mul_inv
          linear_combination -((χ (g * s) : kˣ) : k) * e2 - e3
        have z1 := z 1 U.one_mem
        have z2 := z u hu
        rw [mul_one] at z1
        rw [map_mul, Units.val_mul] at z2
        apply hy
        linear_combination ((χ u : kˣ) : k) ^ 2 * z1 - z2
    refine irr2 (W.comp η.ker.subtype) (fun V hV => hII.2 V fun g hg v hv => ?_) (A.val : A →+* PadicAlgCl l)
      Subtype.val_injective (residue A) (χ.comp η.ker.subtype) (fun g => (r g).mat 0 0 + (r g).mat 2 2) (fun g => ?_) (fun g => ?_)
      _ (u := ⟨g₂, hg₂⟩) ?_ ?_ ?_
    · have := hV ⟨g, hg⟩ trivial v hv
      beta_reduce
      rw [← hW g hg]
      exact this
    · show _ = (W g).val.trace
      rw [hW g g.2, Matrix.trace_fin_two, map_add (f := _)]
      rfl
    · have e2 : ∀ i, residue A ((r g).mat i i) = residue A (algebraMap c.O A ((U3.r0 η Ψ g).mat i i)) := fun i =>
        Ideal.Quotient.eq.2 (hr.red.red g i i)
      rw [map_add (f := _), e2, e2, ← map_inv]
      show _ = residue A (algebraMap c.O A (Ψ g : c.Oˣ)) + residue A (algebraMap c.O A (Ψ (g : G ℚ Ω)⁻¹ : c.Oˣ))
      simp [U3.GG.mat, U3.tor_val, U3.wt1]
    · rw [Subgroup.mem_subgroupOf, k.gal]
      exact ⟨k.g0.1, hg₂⟩
    · show (W g₂).val.det = 1
      rw [hdet, hmk.ηg]
      simp
    · intro h
      refine (hmk.Ψg.map ((residue A).comp (algebraMap c.O A))).ne_zero ?_
      rw [map_sub, map_pow, map_one, sub_eq_zero]
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val] at h'
      exact h'
  have hirr : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) :=
    Db.irr_of_matIrr (by norm_num) (Base.galOf ℚ L Ω) (fun g => (W g).val)
      (fun V hV => hU V fun g hg v hv => hV g hg v hv) (Base.galEmb ℚ L Ω) (Base.range_galEmb ℚ L Ω).ge _ fun _ => rfl
  obtain ⟨J, hJ⟩ : ∃ J : GL (Fin 2) (Qbar l),
      ∀ M : Matrix (Fin 2) (Fin 2) (Qbar l), M.transpose * J.val * M = M.det • J.val := by
    refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two],
      by simp [Matrix.one_fin_two]⟩, fun M => ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
  have hpair : ∀ s : G ℚ Ω, η s = 1 →
      (W s).val.transpose * (J * (W σ)⁻¹).val * (W (σ * s * σ⁻¹)).val = (J * (W σ)⁻¹).val := fun s hs => by
    have e1 : J * (W σ)⁻¹ * W (σ * s * σ⁻¹) = J * W s * (W σ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [Matrix.mul_assoc, ← Units.val_mul, e1, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, hdet,
      hs, Units.val_mul]
    simp
  have halg : Af.IsAlgChar ι (1 : G ℚ Ω →* (Qbar l)ˣ) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ continuous_const fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, 1, one_pos, fun s _ => by simp⟩
  have hautL : Af.IsAut ι (W.comp (Base.galEmb ℚ L Ω)) :=
    (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hH) ℚ K L Ω hsol ⟨inferInstance, Or.inr ⟨hK2, inferInstance⟩⟩ inferInstance
      inferInstance l ι 2 (by norm_num) (W.comp (Base.galEmb ℚ K Ω)) 1 (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr halg
      (fun _ _ _ _ => rfl) ⟨σ, J * (W σ)⁻¹, H.cc, fun s s' hs => by
        have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
        simp⟩).1 ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 2 _).2.1.2 haut)
  have hcsd : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (W.comp (Base.galEmb ℚ L Ω)) ka) := by
    obtain ⟨hc, art, χ, a, h'⟩ := hka.alg
    have hCL := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH L Ω l ι 2 _).2.1.1 hautL
    have hWL : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ L Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := W.comp (Base.galEmb ℚ K Ω)) L hH hsol (by norm_num) (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr
        ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 1, σ, J * (W σ)⁻¹, halg,
          fun _ _ _ _ => rfl, H.cc, fun s s' hs => by
            have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
            rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
            simp⟩ haut hFl hWit
    refine _root_.UpperTheory.GalN.V.mkCsd'_alt ?_ fun _ => _root_.UpperTheory.V.Z.Win.Dn.twist'_alt hH.toClassicalTheorems ⟨χ, hc, art, a, h'⟩ hc hWL
    refine _root_.UpperTheory.GalN.V.csdOf0_alt hH ℚ L Ω inferInstance l ι 2 (by norm_num) _ σ (J * (W σ)⁻¹) H.cc
      (_root_.UpperTheory.V.Af.twist_invariance_automorphic hH L Ω l ι 2 _ ka hautL ⟨χ, hc, art, a, h'⟩) fun s s' hs => ?_
    have hs' : Base.galEmb ℚ L Ω s' = σ * Base.galEmb ℚ L Ω s * σ⁻¹ := hs
    have hp := hpair _ (hηL s)
    rw [← hs'] at hp
    rw [MonoidHom.zpow_apply, ← hka.conj s s' hs', Units.val_mul (ka s)]
    simp only [Af.tw_val, MonoidHom.comp_apply, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hp]
    rw [mul_comm, mul_smul]
  obtain ⟨s, V, ρ, a1, a2, a3⟩ := hrig A ρ' h1 h3 (W.comp (Base.galEmb ℚ L Ω))
    (fun s => by rw [h2, MonoidHom.comp_apply, hW _ (hηL s)]; rfl) hirr hcsd
    (_root_.UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes L W hfree)
  refine adDown Ω l K L hK2 (hK ▸ hLη) s V 2 _ _ R (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hR ρ ka
    (fun g t ht => ?_) (fun g g' t hg ht => ?_) a3
  · rw [a1]
    show _ • (W (Base.galEmb ℚ L Ω g)).val = _ • (W (Base.galEmb ℚ K Ω t)).val
    rw [ht]
  · have : θ (Base.galEmb ℚ K Ω t) = 1 := Units.ext (by rw [hθ, hηK]; simp)
    rw [← a2 g g' hg]
    exact mul_eq_left.2 this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJDense
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
private theorem UpperTheory.V.Hi.dense_arithmetic_points {O A B T E : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing T] [CommRing E]
    [Algebra O A] [Algebra O B] [Algebra O T] [Algebra O E] [Algebra A T] (lam : A →ₐ[O] B) (f : B →ₐ[O] T)
    (hf : ∀ a, f (lam a) = algebraMap A T a) (P : (A →+* E) → Prop) (G : (B →ₐ[O] E) → Prop)
    (hG : ∀ x : B →ₐ[O] E, P (x.comp lam).toRingHom → G x)
    (hsep : ∀ t : T, (∀ x : T →ₐ[O] E, P (x.toRingHom.comp (algebraMap A T)) → x t = 0) → t = 0) (b : B)
    (hb : ∀ x : B →ₐ[O] E, RingHom.ker f ≤ RingHom.ker x → G x → x b = 0) : b ∈ RingHom.ker f := by
  rw [RingHom.mem_ker]
  refine hsep (f b) fun x hx => hb (x.comp f) (fun y hy => ?_) (hG _ ?_)
  · rw [RingHom.mem_ker] at hy ⊢
    rw [AlgHom.comp_apply, hy, map_zero]
  · have e : ((x.comp f).comp lam).toRingHom = x.toRingHom.comp (algebraMap A T) :=
      RingHom.ext fun y => congrArg x (hf y)
    rw [e]
    exact hx
theorem UpperTheory.V.Hi.dense_of_is_j_unitary_hecke_data :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.Dense J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ h hh b hb
  rcases hJ with ⟨_, rfl⟩ | ⟨hc, hco, f, _, hmap, hsurj, hlam, rfl⟩
  · exact Submodule.mem_top
  have hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis := hP.litN
  obtain ⟨⟨lam, hl⟩, hbr⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight hN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hh
  have hd := (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  have hout := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight hN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _) hd R.a K _ _ hmap
  exact dense_arithmetic_points (Λ.toPair B.u) f hlam (fun x => (hset Q R.τ₀).Good R.θ x lam) (fun x : B.Pt => x.Good h)
    (fun x hx => (hbr lam hl x).2.2 hx) (hout.sep lam (Set.mem_univ _) hd) b hb
end
end

