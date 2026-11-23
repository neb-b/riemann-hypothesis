module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagAb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published GlobalTheory.Pst UpperTheory.V UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Lev.flagAb (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} {w : HeightOneSpectrum (𝓞 L)}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ)
    (ha : IsLocalArtin h a) (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (hr : Continuous r) (hh : Fin n → (L →+* Qbar l) → ℤ)
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ)
    (hψ : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : GlobalTheory.Pst.Induces Bw) (d : IsdRAt (Loc.PP l) Bw r) :
    Lev.AbW (wdAt (Loc.PP l) ι Bw h hj r) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hc := fun i => (UpperTheory.V.Loc.charDR hN h hw ι a ha (ω i) (hh i) (ψ i) (hψ i)).1 O Bw hj
  obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj r (fun i => GlobalTheory.TripleGal.rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [GlobalTheory.TripleGal.rk1]))
  refine (Lev.ssCalc L Ω A w h).1 n _ (fun j => (ω j).comp a) fun s => ?_
  rw [(F₂ (hN.aut.berger.isPstAt T Bw r (Units.continuous_val.comp hr) d)).2 s]
  exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Lev.unlGap :
    UpperTheory.V.Lev.UnlGap := by
  intro F Ω _ _ _ _ _ l _ n M hM m r w hl A hA κ hκ hm i j e
  obtain ⟨χ, hχ, -, hI⟩ := hκ
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  have hψ : KillsMu M (χ j / χ i) := fun s hs => by
    rw [MonoidHom.div_apply, hχ i s hs, hχ j s hs, div_one]
  have hfin : Finite (χ j / χ i).range := (UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ hψ).to_subtype
  have hN : ∀ s, (χ j / χ i) s ^ Nat.card (χ j / χ i).range = 1 := fun s =>
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, s, rfl⟩ : (χ j / χ i).range)))
  have hN0 : Nat.card (χ j / χ i).range ≠ 0 := Nat.card_pos.ne'
  obtain ⟨g, hg, hne⟩ := UpperTheory.V.Ws.Pt.cycIne F Ω l A hv ((m i - (m j + 1)) * Nat.card (χ j / χ i).range)
    (mul_ne_zero (sub_ne_zero.2 (hm i j)) (by exact_mod_cast hN0))
  apply hne
  have h1 := DFunLike.congr_fun e ⟨g, Ine_le_Dec A hg⟩
  rw [MonoidHom.mul_apply, hI i _ hg, hI j _ hg] at h1
  change cycBar F Ω l g ^ m i * χ i g = cycBar F Ω l g ^ m j * χ j g * cycBar F Ω l g at h1
  have h2 : cycBar F Ω l g ^ (m i - (m j + 1)) = (χ j / χ i) g := by
    rw [MonoidHom.div_apply, zpow_sub, zpow_add_one, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h1,
      mul_right_comm, mul_comm]
  rw [zpow_mul, h2, zpow_natCast, hN]
end

