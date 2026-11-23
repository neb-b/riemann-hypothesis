module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0009
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeInj
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem hopR_single {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (i : Fin r) (t : G i) (v : V)
    (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i t) v =
      hopR (ρ.comp (MonoidHom.mulSingle G i)) (U i) t v := by
  have hsing : ∀ {a b : G i}, a⁻¹ * b ∈ U i →
      (Pi.mulSingle i a : ∀ j, G j)⁻¹ * Pi.mulSingle i b ∈ Subgroup.pi Set.univ U := by
    intro a b hab j _
    by_cases hj : j = i
    · subst hj
      simpa using hab
    · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
  let f : G i ⧸ U i → (∀ j, G j) ⧸ Subgroup.pi Set.univ U :=
    Quotient.lift (fun a => (QuotientGroup.mk (Pi.mulSingle i a) : (∀ j, G j) ⧸ Subgroup.pi Set.univ U)) (by
      intro a b hab
      exact QuotientGroup.eq.2 (hsing (QuotientGroup.leftRel_apply.1 hab)))
  have hf : ∀ a : G i, f (QuotientGroup.mk a) = QuotientGroup.mk (Pi.mulSingle i a) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro c c' h
    induction c using QuotientGroup.induction_on with | _ a => ?_
    induction c' using QuotientGroup.induction_on with | _ b => ?_
    rw [hf, hf, QuotientGroup.eq] at h
    have := h i (Set.mem_univ i)
    simpa [QuotientGroup.eq] using this
  unfold hopR
  symm
  refine finsum_mem_eq_of_bijOn f ⟨?_, hinj.injOn, ?_⟩ ?_
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨Pi.mulSingle i u, ?_, ?_⟩
    · intro j _
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
    · rw [hf, Pi.mulSingle_mul]
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨QuotientGroup.mk (u i * t), ⟨u i, hu i (Set.mem_univ i), rfl⟩, ?_⟩
    rw [hf, QuotientGroup.eq]
    intro j _
    by_cases hj : j = i
    · subst hj
      simp
    · simpa [Pi.mulSingle_eq_of_ne hj] using hu j (Set.mem_univ j)
  · intro c _
    have hc : (QuotientGroup.mk (f c).out : (∀ j, G j) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk (Pi.mulSingle i c.out) := by
      rw [QuotientGroup.out_eq', ← hf, QuotientGroup.out_eq']
    have hu := QuotientGroup.eq.1 hc
    calc (ρ.comp (MonoidHom.mulSingle G i)) c.out v
        = ρ ((f c).out * ((f c).out⁻¹ * Pi.mulSingle i c.out)) v := by
          rw [mul_inv_cancel_left]; rfl
      _ = ρ (f c).out (ρ ((f c).out⁻¹ * Pi.mulSingle i c.out) v) := by rw [map_mul]; rfl
      _ = ρ (f c).out v := by rw [hv _ hu]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeInj :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeInj := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e he S U hU D hD d A w hw hUw ν hν M hM
  obtain ⟨r, w', hinj, rfl⟩ : ∃ (r : ℕ) (w' : Fin r → Pl K), Function.Injective w' ∧ im w' = S := by
    refine ⟨S.card, fun j => (S.equivFin.symm j : Pl K), ?_, ?_⟩
    · intro a b h
      exact S.equivFin.symm.injective (Subtype.ext h)
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (S.equivFin.symm j).2
      · intro hx
        exact ⟨S.equivFin ⟨x, hx⟩, by simp⟩
  obtain ⟨i, rfl⟩ : ∃ i, w' i = w := by simpa [im] using hw
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (K := K) (2 + 2) w' hinj
  obtain ⟨-, -, -, -, -, hmem⟩ := hemb ι hι
  have hlev := (levLaws (K := K) (2 + 2) (im w')).1 U hU
  have hsec := secTr μ₂ τ₁ τ₂ κ e he
  have hz := zMem μ₂ τ₁ τ₂ κ e he
  have hZ2 := hz.2 w' ι hinj hι
  have hflat0 : flat 0 (0 : G1 K (2 + 2) → ℂ) = 0 := by
    funext x
    simp [flat]
  refine (injective_iff_map_eq_zero M).2 fun v hv => ?_
  have hfS : IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := (A.onto _).1 ⟨v, rfl⟩
  have hfix := (hD.fix _ hfS.1.cont).1 hfS.2
  have hFφ : FixF (levOn (im w') U) (flat 0 (A.sec v)) := ((hsec.2.1 _ hfS.1.cont).2 _ hlev.2).2 hfix.2
  have hZ : flat 0 (A.sec v) ∈ Zs τ₁ τ₂ κ e (im w') :=
    (hz.1 _ _).2 ⟨_, hfS.1, hfix.1, ⟨U, hU, hfix.2⟩, rfl⟩
  have hWfix : ∀ u ∈ Subgroup.pi Set.univ (fun j => U (w' j)), rS ι u (flat 0 (A.sec v)) = flat 0 (A.sec v) := by
    intro u hu
    have hin : ι u ∈ levOn (im w') U :=
      (hmem U _).2 ⟨u, 1, by simp, fun j => hu j (Set.mem_univ j), fun j => by simp [GM.cf], fun x => by simp [GM.cf, one_mem]⟩
    funext x
    exact hFφ _ hin x
  have hzero : hopR ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i))
      (GLnLocal.iwahori ((w' i).adicCompletion K) (2 + 2)) (Cartan.diagPow ((w' i).adicCompletion K) (2 + 2) ν)
      (flat 0 (A.sec v)) = 0 := by
    have h1 := hM v
    rw [hv, map_zero, hflat0, ← hι i, hopEmb (2 + 2) w' ι hinj hι U hU _ hFφ,
      hopR_single (rS ι) (fun j => U (w' j)) i _ _ hWfix, hUw] at h1
    exact h1.symm
  have hφ : flat 0 (A.sec v) = 0 :=
    iwInj (2 + 2) (w' i) ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (Zs τ₁ τ₂ κ e (im w'))
      (fun g φ hφ => (hZ2 φ hφ).2 _)
      (fun φ hφ => (hZ2 φ hφ).1.preimage (continuous_mulSingle i))
      ν hν _ hZ
      (fun u hu => hWfix _ fun j _ => by
        by_cases hj : j = i
        · subst hj
          simpa [hUw] using hu
        · simpa [Pi.mulSingle_eq_of_ne hj] using (U (w' j)).one_mem)
      hzero
  have hs0 : A.sec v = 0 := hsec.2.2.1 _ _ (hφ.trans hflat0.symm)
  exact A.inj (hs0.trans (map_zero A.sec).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.RigidE
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem transfer {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ}
    {μ : Measure (normOneGL (K := E) (n := a))} [μ.IsHaarMeasure] {μ' : Measure (normOneGL (K := E) (n := b))} [μ'.IsHaarMeasure]
    {π : CuspSub E a} {π' : CuspSub E b} {V : Submodule ℂ (LL μ)} {V' : Submodule ℂ (LL μ')}
    (h : Dp.Carries μ π V) (h' : Dp.Carries μ' π' V')
    (e : (⟨a, CG.mk π⟩ : Σ c, CG E c) = ⟨b, CG.mk π'⟩) :
    a = b ∧ ∀ S m B, At μ' S V' m B → At μ S V m B := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  obtain rfl : π = π' := (Dp.isoEq E a π π').1 (Quotient.exact (eq_of_heq e2))
  refine ⟨rfl, fun S m B hA => ⟨fun τ => ?_, fun w hw => ?_⟩⟩
  · exact (Dp.sInfIff E a μ π V h τ _).2 ((Dp.sInfIff E a μ' π V' h' τ _).1 (hA.1 τ))
  · exact (Dp.sSatIff E a μ π V h w _).2 ((Dp.sSatIff E a μ' π V' h' w _).1 (hA.2 w hw))

private theorem core {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (d' : κ → ℕ) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (μ : ∀ i, Measure (normOneGL (K := E) (n := (d i)))) [∀ i, (μ i).IsHaarMeasure]
    (μ' : ∀ j, Measure (normOneGL (K := E) (n := (d' j)))) [∀ j, (μ' j).IsHaarMeasure]
    (V : ∀ i, Submodule ℂ (LL (μ i))) (V' : ∀ j, Submodule ℂ (LL (μ' j)))
    (hV : ∀ i, IsSummand (μ i) (V i)) (hV' : ∀ j, IsSummand (μ' j) (V' j)) (S : Set (Pl E)) (hS : S.Finite)
    (lam : ι → ℂ) (B : ι → Pl E → Multiset ℂ) (B' : κ → Pl E → Multiset ℂ)
    (hB : ∀ i, ∀ w ∉ S, SSat (μ i) (V i) w (B i w)) (hB' : ∀ j, ∀ w ∉ S, SSat (μ' j) (V' j) w (B' j w))
    (e : ∀ w ∉ S, ∑ j, B' j w = ∑ i, (B i w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam i))) :
    ∃ s : ι ≃ κ, ∀ i, d i = d' (s i) ∧ ∀ S m C, At (μ' (s i)) S (V' (s i)) m C → At (μ i) S (V i) m C := by
  choose π hπ using fun i => (Dp.exCusp E (d i) (μ i) (V i) (hV i)).exists
  choose π' hπ' using fun j => (Dp.exCusp E (d' j) (μ' j) (V' j) (hV' j)).exists
  have hn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (π i) := fun i =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ i)).1
  have hn' : ∀ j, GlobalTheory.DiscSpec.IsNormalised (π' j) := fun j =>
    (Dp.normIff E _ _).2 ((Dp.exSummand E _ _ _ _).1 (hπ' j)).1
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E ι κ d d'
    (fun i => (CG.mk (π i)).twist (GlobalTheory.CuspRep.Model.absC E (lam i)))
    (fun j => (CG.mk (π' j)).twist (GlobalTheory.CuspRep.Model.absC E 0)) hd hd' (by
    filter_upwards [hS.compl_mem_cofinite] with w hw
    choose A hA hA1 using fun i => (Dp.sSatIff E _ (μ i) (π i) (V i) (hπ i) w _).1 (hB i w hw)
    choose A' hA' hA1' using fun j => (Dp.sSatIff E _ (μ' j) (π' j) (V' j) (hπ' j) w _).1 (hB' j w hw)
    refine ⟨fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w), A',
      fun i => PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC (π i) (hA1 i) (lam i), fun j => ?_, ?_⟩
    · rw [PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one]
      exact hA1' j
    · apply Multiset.map_injective (f := fun b : ℂˣ => (b : ℂ)) (fun a b e => Units.ext e)
      have h1 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ)) A' Finset.univ
      have h2 := map_sum (Multiset.mapAddMonoidHom fun b : ℂˣ => (b : ℂ))
        (fun i => (A i).map (· * (GlobalTheory.CuspRep.Model.absC E (lam i)).val w)) Finset.univ
      refine h2.trans (Eq.trans ?_ h1.symm)
      have h3 := e w hw
      simp only [hA, hA'] at h3
      refine Eq.trans ?_ h3.symm
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Function.comp_def, Units.val_mul,
        PositivityTheory.Rg.Rs.StrStepB.absC_val])
  exact ⟨s, fun i => transfer (hπ i) (hπ' (s i))
    (PositivityTheory.Rg.Rs.StrStepB.match_twist (hd i) _ _ (hn i) (hn' _) (hs i)).2⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.rigidE :
    RigidE := by
  intro E _ _ _ τ₁ τ₂ hP S hS m₁ m₂ B₁ B₂ h₁ h₂
  have hs : ∀ j : Fin 2, IsSummand (BW.mu1 E 2) (![τ₁, τ₂] j) := by
    intro j
    fin_cases j
    · exact ⟨hP.irr₁.le, hP.irr₁.closed, hP.irr₁.inv, hP.irr₁.ne, hP.irr₁.irr⟩
    · exact ⟨hP.irr₂.le, hP.irr₂.closed, hP.irr₂.inv, hP.irr₂.ne, hP.irr₂.irr⟩
  have hB : ∀ j : Fin 2, ∀ w ∉ S, SSat (BW.mu1 E 2) (![τ₁, τ₂] j) w (![B₁, B₂] j w) := by
    intro j
    fin_cases j
    · exact h₁.2
    · exact h₂.2
  constructor
  · rintro b ⟨lam, m, B, hA, -, hw⟩
    obtain ⟨s, h⟩ := core b.d (fun _ : Fin 2 => 2) b.pos (fun _ => two_pos) b.μ (fun _ => BW.mu1 E 2) b.V ![τ₁, τ₂]
      b.summand hs S hS lam B ![B₁, B₂] (fun i => (hA i).2) hB fun w hS' => by
        rw [Fin.sum_univ_two]; exact hw w hS'
    refine ⟨by simpa using Fintype.card_congr s, fun i => (h i).1, s.symm 0, s.symm 1,
      s.symm.injective.ne (by decide), (h _).2 _ _ _ ?_, (h _).2 _ _ _ ?_⟩
    · rw [s.apply_symm_apply]; exact h₁
    · rw [s.apply_symm_apply]; exact h₂
  · intro μ _ V hV hA
    obtain ⟨s, -⟩ := core (fun _ : Unit => 2 + 2) (fun _ : Fin 2 => 2) (fun _ => by norm_num) (fun _ => two_pos)
      (fun _ => μ) (fun _ => BW.mu1 E 2) (fun _ => V) ![τ₁, τ₂] (fun _ => hV) hs S hS (fun _ => 0)
      (fun _ w => B₁ w + B₂ w) ![B₁, B₂] (fun _ => hA.2) hB fun w _ => by simp
    simpa using Fintype.card_congr s
end

