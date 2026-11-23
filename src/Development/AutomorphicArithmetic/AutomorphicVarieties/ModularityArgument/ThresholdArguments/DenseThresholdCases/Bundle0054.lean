module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0070
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0050
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepNewAE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.CompatCsdOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.BaseChangeIdentities
theorem bcSpeh_alt : DefiniteN → GlobalTheory.BcSpeh.BcSpeh :=
  fun h => bcSpeh_of ascComp h
end UpperTheory.BaseChangeIdentities
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedIV
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu in
theorem UpperTheory.V.Cu.fourth_initial_of_rank_four_data : AlNe → _root_.UpperTheory.V.Cu.TauExAlt → RankFourAutomorphyOfTensor → RhoExP → TwEx4 → PairOf4 → ResOf4 → ContOf4 → EntOf4 → OverOf4 → WtsOf4 → IrrOf4 →
    AutOf4 → _root_.UpperTheory.V.Af.Hypotheses' → PropEGP → _root_.UpperTheory.V.Cu.SeedIVAlt := by
  intro hne hTau hAQ hRho hTw hPair hRes hCont hEnt hOver hWts hIrr hAut hH hP Ω _ _ _ l _ c D T₀ hc hok h4 ι 𝔞
  have hg : D.Good := hc.1
  obtain ⟨K', _, hq⟩ := h4.quad
  have hfix : ∀ (T : Tower D) (g : G T.F Ω), resQ T.F g ∈ T.F.fixingSubgroup := fun T g x => g.commutes x
  have hg0 : resQ T₀.F T₀.g0 ∉ K'.fixingSubgroup := by
    intro hm
    have h1 := hq.on _ hm
    apply hok.dist 0 1 (by decide)
    have h2 : residue c.O (((chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 1 (resQ T₀.F T₀.g0))⁻¹) ^ (1 : ℤ) *
        (chi D T₀.pr 0 (resQ T₀.F T₀.g0) * (chi D T₀.pr 2 (resQ T₀.F T₀.g0))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = 1 := h1
    rw [zpow_one, zpow_zero, mul_one] at h2
    have h3 := congrArg (· * residue c.O (chi D T₀.pr 1 (resQ T₀.F T₀.g0) : c.O)) h2
    simp only [← map_mul, ← Units.val_mul, inv_mul_cancel_right, one_mul] at h3
    exact h3
  obtain ⟨m, c₀, κ, hκ⟩ := hTau hH Ω l ι K' hg.l_odd hq.deg hq.imag hq.disc hq.split ⟨D.cc, hg.isCC⟩ _ hg0
  obtain ⟨w, θ, k, ρ, c₁, h, ρ₁, x, hw, hsp, hθl, hθm, hB, hk, hE, ⟨hI, hrw⟩, h₀, hM⟩ :=
    hRho hP Ω l c D T₀ hc hok h4 ι (2 * (m * 9) + 3) c₀
  obtain ⟨j, j1, j9, hj⟩ := hAQ Ω l ι K' hq.deg hq.imag ρ hE.cont hE.aut hI hrw _ m c₁ κ hg0 (hκ c₁ h₀ 1 le_rfl)
  obtain ⟨τ, s, hτ⟩ := hκ c₁ h₀ j j1
  obtain ⟨δ, hδ⟩ := hTw Ω l c D T₀ hc k (by omega) hk
  have hbig : 2 * (m * j) + 3 ≤ k := le_trans (by have := Nat.mul_le_mul_left m j9; omega) hB
  obtain ⟨hunr, hdies⟩ := UpperTheory.theta_unramified_of_kills_roots_of_unity Ω l w hw θ hθl hθm
  let d : Dat Ω l := ⟨ι, c, D, T₀, hc, hok, K', hq, k, m * j, hbig, hk, δ, hδ, θ, ρ, hE, hI, c₁, h, ρ₁, x, hM, τ, s, κ ^ j, hτ,
    (hj ρ₁ τ s hM.iso hτ).1, w, hw, hsp, hunr⟩
  have hf : ∀ y ∈ maximalIdeal c₁.O, 𝔞.red c₁ y = 0 := fun y hy =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c₁) y hy)
  have hred : 𝔞.red c = (𝔞.red c₁).comp (inc h) := RingHom.ext fun y => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h y).symm
  have hle : T₀.Le T₀ := ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩
  obtain ⟨r1, r2, -, r3⟩ := hRes Ω l d T₀ hle {w} 𝔞.k (𝔞.red c₁) hf
  refine ⟨w, (d.Q T₀).map (𝔞.red c₁), hw, hsp, ⟨?_, ?_, (hCont Ω l d T₀).2 _ _ hf⟩, r2,
    fun T hT tok hd => ⟨c₁, h, d.Q T, ⟨?_, (hCont Ω l d T).1, ?_, ?_⟩, hOver Ω l d T hT _ _ hf,
      (hRes Ω l d T hT ∅ 𝔞.k (𝔞.red c₁) hf).2.2.1, hEnt Ω l d T hT tok _ _ hf⟩⟩
  · rw [hred]
    exact hPair Ω l d T₀ hle hok {w} 𝔞.k (𝔞.red c₁) (fun g _ => r3 g) fun A hA g hg =>
      hunr A (fun p hp => hA p (Finset.mem_insert_of_mem hp)) hg
  · rw [hred]
    exact r1
  · have := hPair Ω l d T hT tok ∅ c₁.O (RingHom.id _) (fun g hg => hM.det g (hdies T.F hd hg)) fun A _ g _ =>
      hdies T.F hd (hfix T g)
    have e : (d.Q T).map (RingHom.id c₁.O) = d.Q T := by
      ext <;> rfl
    rwa [e, RingHom.id_comp] at this
  · exact (hRes Ω l d T hT ∅ _ (residue c₁.O) fun y hy => (residue_eq_zero_iff _).2 hy).1
  · exact _root_.UpperTheory.V.Cu.tower_is_initial_of_ok hne hWts hIrr hAut Ω l d T hT tok (hj ρ₁ τ s hM.iso hτ).2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrRepNewAE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf
private theorem tend : Filter.Tendsto (fun w : Pl ℚ => normV w) Filter.cofinite Filter.cofinite :=
  Function.Injective.tendsto_cofinite fun w w' e => HeightOneSpectrum.ext <| by
    rw [(places w).2.1, (places w').2.1]
    exact congrArg (fun n : ℕ => Ideal.span {(n : 𝓞 ℚ)}) e
theorem UpperTheory.V.Br.repNewAE_of_printsH_of_repEig :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Br.RepEig → UpperTheory.V.Br.RepNewAE := by
  intro hP hR k hk j π hπ
  have hk1 : 1 ≤ k := by omega
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ (-s)
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ (-s)
  have hi : ∀ v, (π.twist χ).HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := fun v => by
    have := (hπ v).twist χ
    rw [absExpo ℚ (-s) v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  obtain ⟨N, _, ψ, g, hg⟩ := hR k hk _ hi
  obtain ⟨f, _, h, hf, ha⟩ := UpperTheory.V.Br.minNew N k hk1 ψ g
  have hc := _root_.UpperTheory.V.Br.charEq_sv_alt hP k N f.M (by omega) ψ f.χ g h ha
  refine ⟨f, ?_⟩
  filter_upwards [hg, tend.eventually ha, tend.eventually hc] with w ⟨α, β, hsat, hsum, hprod⟩ h1 h2
  have hp := (places w).1
  have hq := (places w).2.2.1
  have hu : (χ⁻¹).UnrAt w := fun u hu => by
    have := hE.1 w u hu
    exact inv_eq_one.2 this
  have h3 := hsat.twist hu
  rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h3
  refine ⟨_, h3, ?_⟩
  have hq0 : (0 : ℝ) < normV w := by exact_mod_cast hp.pos
  have hval0 : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-(-s)) : ℝ) : ℂ) := by
    rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
  have hval : (((χ⁻¹).val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, hval0, ← Complex.ofReal_inv, ← Real.rpow_neg hq0.le, neg_neg]
  set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
  have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * (χ⁻¹).val w : ℂˣ) : ℂ)) =
      r * a := fun a => by
    have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
        (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 1
      rw [hs]; push_cast; ring
    rw [hr, this, Units.val_mul, hval]; push_cast; ring
  have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
    rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
    push_cast; rfl
  have hfa : f.a (normV w) = r * ((α : ℂ) + β) := by
    rw [← hsum, ← h1 hp, Newform.a, Eigenform.a, hf]
  simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
    Multiset.singleton_add, key]
  rw [Newform.heckePoly, hfa, ← h2 hp, ← hprod, ← hrr]
  simp only [Units.val_mul, C_mul, C_add]
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Chain2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)
theorem UpperTheory.V.Ws.deep_tower_residue_chain_exists :
    CohomologyHyp → _root_.UpperTheory.V.Ws.SeedIIAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx2 D → T₀.Ok → T₀.Two → TameL l T₀.F → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' → (T.fr ∅).Chain (𝔞.red c) c₀' (Q.map (𝔞.red c₁)) := by
  intro hP hS Ω _ _ _ l _ c D T₀ hC hO hT hL ι 𝔞 c₀ hc₀
  have hG : D.Good := hC.1
  have hF : T₀.Fit := ⟨hO, Or.inl ⟨hC, hT⟩⟩
  have ha : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hrt := (Chain.rtFacts D hG T₀ hO _ _ ha).1
  obtain ⟨s₀, hs₀, ho₀⟩ := Chain.exists_residual_datum_over_restriction_to_rationals hP D T₀ hF _ _ ha c₀ hc₀.res ⟨hc₀.supp, fun _ => hc₀.flag⟩
  have hq₀ := goodQ D hG T₀ hF _ _ ha _ c₀ s₀ hc₀ hrt ho₀ hs₀
  obtain ⟨W, s, -, -, hW, hs, -, hsQ, -, hsP, -, -, hsA⟩ :=
    gysinAl hP D T₀ hF _ _ ha ∅ (by simp) s₀ s₀ hs₀ hs₀ (hq₀ ∅).2.1 (hq₀ ∅).2.1
  obtain ⟨T₁, h01, hL1, hD⟩ := diesEx D hG T₀ hL hO W hW
  refine ⟨T₁, h01, hL1, fun T h1 hdeep => ?_⟩
  have h0 : T₀.Le T := (leFit D hG T₀ T₁ h01).2.2.2.2.2.2 T h1
  obtain ⟨lO, lT, -, -, lF, -⟩ := leFit D hG T₀ T h0
  have tO := lO hO
  have tT := lT hT
  have tF := lF hF
  have hDT : ∀ w ∈ W, Dies l w T.F := fun w hw θ h1' h2 =>
    (IntermediateField.fixingSubgroup_antitone h1.le).trans (hD w hw θ h1' h2)
  obtain ⟨c₁, h, Q, hQ, hQV, hQE⟩ := hS Ω l c D T hC tO tT hdeep ι
  refine ⟨c₁, h, Q, hQ, fun c₀' ho hr => ?_⟩
  obtain ⟨sR, sV, sE⟩ := _root_.UpperTheory.V.Ws.Chain.isRes_map_red_and_inV_ent_map_red_of_map_residue D T ι 𝔞 h Q hQ
  have sV := sV hQV
  obtain ⟨c₃, r₃, o₃⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s hs (Or.inr (Or.inl hsQ.1))
  obtain ⟨t, rt, ot⟩ := restrT D hG T₀ T h0 hF _ _ ha W hW hDT s₀ (hq₀ W).1 (Or.inr (Or.inr hs₀))
  have hsP' : s.In nP := ⟨fun g => supp_mono (by decide) (hsQ.1 g), hsQ.2⟩
  have hsM : Supp nM s.r := fun g => supp_mono (by decide) (hsQ.1 g)
  obtain ⟨-, f2, f3, f4, -, -, f7, -⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s s₀ c₃ t hs (hq₀ W).1 r₃ rt o₃ ot
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := overFacts D hG T₀ T h0 hF _ _ ha W ∅ s₀ s t c₃ (hq₀ W).1 hs rt r₃ ot o₃
  obtain rfl : c₀' = t := g8 c₀ _ hc₀.res.pair ho₀ c₀' hr ho
  have q₃ : Supp qQ c₃.r := f2 _ hsQ.1
  have i₃ : c₃.In nP := f3 hsP'
  have m₃ : Supp nM c₃.r := f2 _ hsM
  have p₃ : c₃.SamePs c₀' := f4 hsP' (hq₀ W).2.1 hsP
  have a₃ : Ent c₃.r (-wAl) := (f7 hsM).1 hsA
  obtain ⟨-, i₀, g₀⟩ := goodQ D hG T tF _ _ ha (resQ T₀.F T₀.g0) c₀ c₀' (h0.pr ▸ hc₀) (h0.pr ▸ hrt) ho hr ∅
  have ok : (T.fr ∅).Ok (𝔞.red c) := (std hP D T tF ∅ c le_rfl).2 _ _ ha
  have hmu : ∀ v, ∀ s ∈ (T.fr ∅).Mu v, s ∈ (T.fr ∅).Gv v := fun v s hs => hs.1
  have hrb := (Chain.rtFacts D hG T tO _ _ ha).2
  obtain ⟨c₄', r₄', u₄', n₄', e₄'⟩ := Chain.levi (T.fr ∅) _ hmu c₃ r₃ m₃
  obtain ⟨c₄, r₄, e₄, n₄⟩ := Chain.movePs (T.fr ∅) _ ok.mul hmu
    (fun v s hs => (hrb _ _).2 (tT.atL _ (T.ovl v) s hs)) c₄' r₄' u₄' n₄' fun v => (Q.map (𝔞.red c₁)).n v 2 0
  have u₄ : Supp {-wAl} c₄.r := e₄ ▸ u₄'
  have m₄ : Supp nM c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have v₄ : Supp vV c₄.r := fun g => supp_mono (by decide) (u₄ g)
  have al : c₃.SameAl c₄ := ⟨fun g => by rw [e₄, e₄'.1], fun v => ((n₄ v).2.1.trans (e₄'.2 v)).symm⟩
  have a₄ : Ent c₄.r (-wAl) := by
    obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).2 m₃).1 a₃
    exact ((Chain.entIff (T.fr ∅) (𝔞.red c) c₄ r₄).2 m₄).2 ⟨g, al.1 g ▸ hg⟩
  have G₀ : (T.fr ∅).Good (𝔞.red c) c₀' := g₀.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x))
  have G₃ : (T.fr ∅).Good (𝔞.red c) c₃ := by
    by_cases hp : Ent c₃.r (-wPs)
    · exact Or.inl ⟨hp, Or.inr a₃⟩
    rcases g₀ with x | x
    · obtain ⟨g, hg⟩ := ((Chain.entIff (T.fr ∅) (𝔞.red c) c₀' hr).1 i₀.1).1 x.1
      exact absurd (((Chain.entIff (T.fr ∅) (𝔞.red c) c₃ r₃).1 i₃.1).2 ⟨g, p₃.1 g ▸ hg⟩) hp
    refine Or.inr (Or.inr (Or.inl ⟨⟨fun g i j hij hw => ?_, fun v => ⟨i₃.2 v, p₃.2 v ▸ (x.1.2 v).2⟩⟩, a₃⟩))
    by_cases hq : wt i j = -wPs
    · by_contra hne
      exact hp ⟨g, i, j, hq, hne⟩
    · exact q₃ g i j hij (by revert hw hq; revert i j; decide)
  have G₄ : (T.fr ∅).Good (𝔞.red c) c₄ :=
    Or.inr (Or.inr (Or.inl ⟨⟨v₄, fun v => ⟨(n₄ v).1, (n₄ v).2.2 ▸ (sV.2 v).2⟩⟩, a₄⟩))
  have Gs : (T.fr ∅).Good (𝔞.red c) (Q.map (𝔞.red c₁)) := by
    rcases hQE with x | x
    · exact Or.inr (Or.inr (Or.inl ⟨sV, sE _ x⟩))
    refine Or.inr (Or.inr (Or.inr ⟨sV, sE _ x.1, sE _ x.2, fun v => ?_⟩))
    obtain ⟨g, hg, hne⟩ := tT.bigL _ (T.ovl v)
    exact ⟨g, hg, fun h1 => hne (by rw [(hrb _ _).1 h1, one_pow])⟩
  have L₁ := lineP (T.fr ∅) _ ok c₀' c₃ hr r₃ i₀ i₃ ⟨fun g => (p₃.1 g).symm, fun v => (p₃.2 v).symm⟩
  have L₂ := lineM (T.fr ∅) _ ok c₃ c₄ r₃ r₄ m₃ m₄ al
  have L₃ := lineP (T.fr ∅) _ ok c₄ _ r₄ sR ⟨fun g => supp_mono (by decide) (v₄ g), fun v => (n₄ v).1⟩
    ⟨fun g => supp_mono (by decide) (sV.1 g), fun v => (sV.2 v).1⟩
    ⟨fun g => (v₄ g 2 0 (by decide) (by decide)).trans (sV.1 g 2 0 (by decide) (by decide)).symm, fun v => (n₄ v).2.2⟩
  exact ⟨G₀, ((Relation.ReflTransGen.single ⟨G₃, L₁⟩).tail ⟨G₄, L₂⟩).tail ⟨Gs, L₃⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ClassicalFixedByIwahori
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem UpperTheory.V.Ws.ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)
private theorem UpperTheory.V.Ws.ch_core {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hS : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hg : Φ.Good ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes} := (List.finite_toSet redTypes).to_subtype
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (red Φ l a hS d C hB c hc hg R _ hdef S.1 S.2).trans_lt (by exact_mod_cast hN1))
    (fun t q hq hle hr => ch_num
      (fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
        ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx))
        fun S hS => hr ⟨S, hS⟩))
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2) _ hPQ.2.2
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) fun S hS => hA ⟨S, hS⟩)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]
theorem UpperTheory.V.Ws.residual_charpoly_rank_four :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C → 30 * (C + 1) * (C + 1) ≤ T.d →
      ∀ x : X.A →ₐ[c'.O] ResidueField c'.O, (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) → (T.fr ∅).Good ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x) := by
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg ⟨q₀, hq₀, hq₀x, hq₀J⟩ q hq hqx
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, _, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact ch_core hS X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => _root_.UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hg f hdef hPQ ih
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuPChainIV
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Ws.Chn
end UpperTheory.V.Cu.RankFourChainReduction
open UpperTheory.V.Cu UpperTheory.V.Ws.Chn UpperTheory.V.Cu.RankFourChainReduction in
theorem UpperTheory.V.Cu.chainIV_alt : _root_.UpperTheory.V.Cu.RankFourChainReductionDense := by
  intro hC hH hS Ω _ _ _ l _ c D T₀ h3 hok h4 htame ι 𝔞 c₀ hc₀
  have hG : D.Good := h3.1
  have hF : T₀.Fit := hH D T₀ h3 hok h4
  have ha := red_zero 𝔞 c
  have ok0 : (T₀.fr ∅).Ok (𝔞.red c) := (std hC D T₀ hF ∅ c le_rfl).2 _ _ ha
  obtain ⟨w, s, hw, hsp, hs, hsM, hseed⟩ := hS Ω l c D T₀ h3 hok h4 ι 𝔞
  obtain ⟨p0, hp0, hov0⟩ := UpperTheory.exists_residualRep_restriction_of_latticeShape D hG T₀ hF _ _ ha ok0 c₀ hc₀
  obtain ⟨-, hp0P, -⟩ := goodQ D hG T₀ hF _ _ ha _ c₀ p0 hc₀ (fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw) hov0 hp0 ∅
  obtain ⟨W1, p2, hW1, hW1s, hp2, hp2Q, hp2A, hp2E⟩ :=
    gysinPs hC D T₀ hF _ _ ha {w} (by simpa using ⟨hw, hsp⟩) s hs hsM
  obtain ⟨W2, p3, p4, hW2, hW2s, hp3, hp4, hp3Q, hp4Q, h30, h42, h34, h3E⟩ :=
    gysinAl hC D T₀ hF _ _ ha W1 hW1s p0 p2 (res_mono T₀ (Finset.empty_subset _) hp0) hp2 hp0P (qP hp2Q)
  obtain ⟨T₁, hL1, ht1, hd1⟩ := diesEx D hG T₀ htame hok W2 hW2s
  refine ⟨T₁, hL1, ht1, fun T hL _ => ?_⟩
  have hT : T₀.Le T := (leFit D hG T₀ T₁ hL1).2.2.2.2.2.2 T hL
  obtain ⟨lo, -, -, -, lf, -, -⟩ := leFit D hG T₀ T hT
  have hd : ∀ w ∈ W2, Dies l w T.F := fun w hw => dies_mono hL.le (hd1 w hw)
  obtain ⟨c₁, h, Q, hQ, hovs, hQA, hQB, hQT⟩ := hseed T hT (lo hok) (hd w (hW2 (hW1 (Finset.mem_singleton_self w))))
  refine ⟨c₁, h, Q, hQ, fun u hu hur => ?_⟩
  have okT : (T.fr ∅).Ok (𝔞.red c) := (std hC D T (lf hF) ∅ c le_rfl).2 _ _ ha
  have hq := _root_.UpperTheory.V.Ws.Chn.seed_res_alt T 𝔞 hQ
  replace hs := res_mono T₀ (hW1.trans hW2) hs
  replace hp0 := res_mono T₀ (Finset.empty_subset W2) hp0
  replace hp2 := res_mono T₀ hW2 hp2
  have R := fun x hx => restrT D hG T₀ T hT hF _ _ ha W2 hW2s hd x hx (Or.inl h4.five)
  obtain ⟨q0, hq0, o0⟩ := R p0 hp0
  obtain ⟨q2, hq2, o2⟩ := R p2 hp2
  obtain ⟨q3, hq3, o3⟩ := R p3 hp3
  obtain ⟨q4, hq4, o4⟩ := R p4 hp4
  have O := overFacts D hG T₀ T hT hF _ _ ha W2 ∅
  obtain ⟨-, -, -, a1, -, -, -, a2⟩ := O p0 p3 q0 q3 hp0 hp3 hq0 hq3 o0 o3
  obtain rfl : u = q0 := a2 c₀ _ hc₀.res.pair hov0 u hur hu
  obtain ⟨-, b0, b1, -, b2, -, b4, -⟩ := O p3 p4 q3 q4 hp3 hp4 hq3 hq4 o3 o4
  obtain ⟨-, c0, c1, c2, -, -, -, -⟩ := O p4 p2 q4 q2 hp4 hp2 hq4 hq2 o4 o2
  obtain ⟨-, d0, d1, -, d2, d3, -, -⟩ := O p2 s q2 _ hp2 hs hq2 hq o2 hovs
  obtain ⟨-, e0, -, -, -, -, -, -⟩ := O s s _ _ hs hs hq hq hovs hovs
  have hlat : LatShape D T.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ := hT.pr ▸ hc₀
  have hrt : ∀ w ∈ roots, 𝔞.red c ((frQ D T.pr (resQ T₀.F T₀.g0)).rt w (resQ T₀.F T₀.g0)) ≠ 1 := by
    rw [hT.pr]; exact fun w hw => rt_ne (Φ := T₀.fr ∅) ok0 w hw
  obtain ⟨-, uP, ug⟩ := goodQ D hG T (lf hF) _ _ ha _ c₀ u hlat hrt hu hur ∅
  have P3 := b1 (qP hp3Q)
  have P4 := c1 (qP hp4Q)
  have P2 := d1 (qP hp2Q)
  have M3 := b0 _ (qM hp3Q.1)
  have M4 := c0 _ (qM hp4Q.1)
  have M2 := d0 _ (qM hp2Q.1)
  have Ms := e0 _ hsM
  have s03 := a1 hp0P (qP hp3Q) (samePs_symm h30)
  have s34 := b2 (qM hp3Q.1) (qM hp4Q.1) h34
  have s42 := c2 (qP hp4Q) (qP hp2Q) h42
  have s2s := d2 (qM hp2Q.1) hsM hp2A
  have A3 := (b4 (qM hp3Q.1)).1 h3E
  have E2 := d3 (qP hp2Q).1 hp2E
  have g0 : Good4 (T.fr ∅) (𝔞.red c) u :=
    Or.inl (ug.elim (fun x => Or.inl ⟨x.1, Or.inl x.2⟩) fun x => Or.inr (Or.inr (Or.inl x)))
  have g3 : Good4 (T.fr ∅) (𝔞.red c) q3 :=
    Or.inl (ug.elim (fun x => Or.inl ⟨(samePs_ent hur hq3 uP.1 P3.1 s03).1 x.1, Or.inr A3⟩)
      fun x => Or.inr (Or.inr (Or.inl ⟨samePs_inV hq3 P3 s03 x.1, A3⟩)))
  have g4 : Good4 (T.fr ∅) (𝔞.red c) q4 :=
    Or.inl (Or.inl ⟨(samePs_ent hq4 hq2 P4.1 P2.1 s42).2 E2, Or.inr ((sameAl_ent hq3 hq4 M3 M4 s34).1 A3)⟩)
  have g2 : Good4 (T.fr ∅) (𝔞.red c) q2 :=
    Or.inr (Or.inl ⟨inA_of hq2 (d0 _ hp2Q.1) s2s hQA, E2⟩)
  have gs : Good4 (T.fr ∅) (𝔞.red c) (Q.map (𝔞.red c₁)) := Or.inr (Or.inr ⟨hQA, hQB, hQT⟩)
  exact ⟨g0, (((Relation.ReflTransGen.single ⟨g3, lineP _ _ okT _ _ hur hq3 uP P3 s03⟩).tail
    ⟨g4, lineM _ _ okT _ _ hq3 hq4 M3 M4 s34⟩).tail ⟨g2, lineP _ _ okT _ _ hq4 hq2 P4 P2 s42⟩).tail
    ⟨gs, lineM _ _ okT _ _ hq2 hq M2 Ms s2s⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsoAltAlt
section
noncomputable abbrev UpperTheory.V.Z.Win.WitA.isobaricDense := @UpperTheory.V.Z.Win.WitA.iso'
end

