module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PStepSplit
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.stepSplit :
    StableOf → ResEmbCompat → LblIso → ∀ P₀, StepAt P₀ id := by
  intro hS hC hI P₀ K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp n hn π P hW A Θ hΘ v w hsplit hunr e e' he he' τ τ' hτ hτ' a hP ha
  refine ⟨a, Relation.ReflTransGen.refl, ?_⟩
  obtain ⟨-, hSL⟩ := hS K M hp n hn π P hW
  obtain ⟨r, j, h1, h2, h3⟩ := hC K M Ω A v w e e' he he'
  have hs : UpperTheory.ConvolutionTheory.GM.Split M v := hsplit
  let i : v.adicCompletion K ≃+* w.1.adicCompletion M :=
    RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs w⟩
  have hi : ∀ x, i x = completionMap v w.1 x := fun _ => rfl
  have hic : Continuous i := continuous_completionMap v w.1
  have hal : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x) := fun x => by
    rw [hi, completionMap_algebraMap, IsScalarTower.algebraMap_apply K M (w.1.adicCompletion M)]
  obtain ⟨f, hf⟩ := hSL v w.1 i hic hal τ τ' hτ hτ'
  have he0 : w.1.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 K) w.1.asIdeal).ne'
  have hle : ∀ x y : w.1.adicCompletion M, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (w.1.adicCompletion M)) Valued.v x y
  have hle' : ∀ x y : v.adicCompletion K, valuation _ x ≤ valuation _ y ↔ Valued.v x ≤ Valued.v y := fun x y =>
    ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v x y
  have hv : ∀ x : v.adicCompletion K, valuation _ (i x) ≤ 1 ↔ valuation _ x ≤ 1 := fun x => by
    have a1 := hle (i x) (i 1)
    have a2 := hle' x 1
    rw [map_one (valuation (v.adicCompletion K))] at a2
    rw [map_one i, map_one (valuation (w.1.adicCompletion M))] at a1
    rw [a1, a2, ← map_one i, hi, hi, valued_completionMap, valued_completionMap]
    exact pow_le_pow_iff_left₀ zero_le zero_le he0
  have hcond : ∀ (x : 𝒪[v.adicCompletion K]) (y : 𝒪[w.1.adicCompletion M]), (y : w.1.adicCompletion M) = i x →
      j (algebraMap _ _ (IsLocalRing.residue _ x)) = algebraMap _ _ (IsLocalRing.residue _ y) :=
    fun x y hy => by rw [h2, h1 x y hy]
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom :=
    MonoidHom.ext fun x => congrArg Θ (h3 x)
  exact hI _ _ i hv j hcond (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ f hf a (by rw [hθ]; exact ha)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSubqMap
section
namespace UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

section SlopeTestRemainingChoices

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori
open GlobalTheory.Parabolic (mem_fixed)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = N} {W V Z : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

private theorem isSmooth_sub (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    IsSmooth S.toRepresentation := fun y => by
  have : {g : GL (Fin N) k | S.toRepresentation g y = y} =
      {g : GL (Fin N) k | parInd (stdBlocks d hd) ρ g y.1 = y.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_parInd _ _ y.1

private theorem levelZeroMap_surjective {S : Subrepresentation (parInd (stdBlocks d hd) ρ)}
    {π : Representation ℂ (GL (Fin N) k) V} (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) : Function.Surjective (levelZeroMap f) := by
  intro v
  obtain ⟨u0, hu0⟩ := hf v.1
  obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (isSmooth_sub S) DepthZero.isCompact_KOne₁
    f.toLinearMap u0 fun h hh => by
      show f (S.toRepresentation h u0) = f u0
      rw [f.isIntertwining, hu0]
      exact mem_fixed.1 v.2 h hh
  exact ⟨⟨u, hu⟩, Subtype.ext (e.trans hu0)⟩

private def evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    fixed S.toRepresentation (KOne k (Fin N)) →ₗ[ℂ] W where
  toFun u := (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOne_redK (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (κ : KO k (Fin N)) (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S (levelZero S.toRepresentation (redK k (Fin N) κ) u) =
      (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 κ := by
  show ((levelZero S.toRepresentation (redK k (Fin N) κ) u).1.1 : IndSp (stdBlocks d hd) ρ).1.1 1 = _
  rw [levelZero_apply]
  show ((parInd (stdBlocks d hd) ρ (κ : GL (Fin N) k) u.1.1 : IndSp (stdBlocks d hd) ρ)).1.1 1 = _
  rw [parInd_apply, one_mul]

private theorem val_mul_of_mem (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) (x : GL (Fin N) k) {c : GL (Fin N) k}
    (hc : c ∈ KOne k (Fin N)) :
    (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 (x * c) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 x := by
  have h : S.toRepresentation c u.1 = u.1 := mem_fixed.1 u.2 c hc
  have h2 : parInd (stdBlocks d hd) ρ c u.1.1 = u.1.1 := congrArg Subtype.val h
  exact congrArg (fun F : IndSp (stdBlocks d hd) ρ => F.1.1 x) h2

private theorem leviKOne_le_leviK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} {d : Fin s → ℕ} :
    leviKOne k (fun a => Fin (d a)) ≤ leviK k (fun a => Fin (d a)) := by
  intro l hl
  unfold leviKOne at hl
  unfold leviK
  rw [Subgroup.mem_pi] at hl ⊢
  exact fun a ha => GlobalTheory.StepData.KOne_le_KO (hl a ha)

private theorem evalOne_mem_fixed (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S u ∈ fixed ρ (leviKOne k fun a => Fin (d a)) := by
  rw [mem_fixed]
  intro l hl
  have hpar := leviEmb_mem_parab k (stdBlocks d hd) l
  have hlaw := parInd_law (stdBlocks d hd) ρ (u.1.1 : IndSp (stdBlocks d hd) ρ) ⟨_, hpar⟩ 1
  have hK : leviEmb k (stdBlocks d hd) l ∈ KOne k (Fin N) := jLevi_le_KOne _ ⟨l, hl, rfl⟩
  have h4 := val_mul_of_mem S u 1 hK
  rw [one_mul] at h4
  simp only [mul_one, leviProj_leviEmb, deltaHalf_of_mem_leviK (leviKOne_le_leviK hl)] at hlaw
  show ρ l ((u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  rw [h4] at hlaw
  simpa using hlaw.symm

private theorem val_of_redK_mem (hPF : ParaFactor) (F : IndSp (stdBlocks d hd) ρ)
    (hF : ∀ x, ∀ c ∈ KOne k (Fin N), F.1.1 (x * c) = F.1.1 x)
    (κ₀ : KO k (Fin N)) (hκ : redK k (Fin N) κ₀ ∈ parab 𝓀[k] (stdBlocks d hd)) :
    ∃ x : leviK k fun a => Fin (d a),
      redLevi k _ x = leviProj 𝓀[k] (stdBlocks d hd) ⟨redK k (Fin N) κ₀, hκ⟩ ∧
      F.1.1 κ₀ = ρ (x : Levi k fun a => Fin (d a)) (F.1.1 1) := by
  have hg : (κ₀ : GL (Fin N) k) ∈ parahoric k (stdBlocks d hd) := (coe_mem_levelPre κ₀).2 hκ
  obtain ⟨p, x, -, hpx, hred, c, hc, hgp⟩ := (hPF k (stdBlocks d hd)).1 ⟨κ₀, hg⟩
  have h3 := parInd_law (stdBlocks d hd) ρ F p 1
  rw [mul_one, hpx, deltaHalf_of_mem_leviK x.2, Units.val_one, one_smul] at h3
  have h4 : (κ₀ : GL (Fin N) k) = p * c := hgp
  refine ⟨x, hred, ?_⟩
  rw [h4, hF _ c hc]
  exact h3


set_option maxHeartbeats 1000000 in
private theorem evalOne_parab (hPF : ParaFactor)
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) (h : parab 𝓀[k] (stdBlocks d hd))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    Φ (evalOne S (levelZero S.toRepresentation (h : GL (Fin N) 𝓀[k]) u)) =
      κ (leviProj 𝓀[k] (stdBlocks d hd) h) (Φ (evalOne S u)) := by
  rcases h with ⟨h, hmem⟩
  obtain ⟨κ₀, rfl⟩ := redK_surjective h
  obtain ⟨x, hx1, hx2⟩ := val_of_redK_mem hPF (u.1.1 : IndSp (stdBlocks d hd) ρ)
    (fun y c hc => val_mul_of_mem S u y hc) κ₀ hmem
  exact (congrArg Φ ((evalOne_redK S κ₀ u).trans hx2)).trans
    ((hΦ x _).trans (congrArg (fun g => κ g (Φ (evalOne S u))) hx1))

private theorem eq_zero_of_evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N)))
    (hu : ∀ γ : GL (Fin N) 𝓀[k], evalOne S (levelZero S.toRepresentation γ u) = 0) : u = 0 := by
  have hF : (u.1.1 : IndSp (stdBlocks d hd) ρ) = 0 :=
    UpperTheory.TNZ.step_indDetK k s N d hd W ρ _ 0 fun κ hκ => by
      have := hu (redK k (Fin N) ⟨κ, hκ⟩)
      rw [evalOne_redK] at this
      exact this
  exact Subtype.ext (Subtype.ext hF)

private theorem main (hPF : ParaFactor) {π : Representation ℂ (GL (Fin N) k) V}
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (hinj : ∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0)
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (sec : fixed π (KOne k (Fin N)) →ₗ[ℂ] fixed S.toRepresentation (KOne k (Fin N)))
    (hs : ∀ g x, sec (levelZero π g x) = levelZero S.toRepresentation g (sec x))
    (hinv : Function.Injective sec)
    (hfix : fixed π (KOne k (Fin N)) ≠ ⊥) :
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x) := by
  obtain ⟨x0, hx0mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  let y0 : fixed π (KOne k (Fin N)) := ⟨x0, hx0mem⟩
  have hsx : sec y0 ≠ 0 := by
    intro h0
    apply hx0
    have h1 := hinv (h0.trans (map_zero sec).symm)
    exact congrArg Subtype.val h1
  have hγ : ∃ γ, evalOne S (levelZero S.toRepresentation γ (sec y0)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsx (eq_zero_of_evalOne S _ hc)
  obtain ⟨γ, hγ⟩ := hγ
  refine ⟨Φ ∘ₗ (evalOne S ∘ₗ sec), ?_, ?_⟩
  · intro h0
    apply hγ
    apply hinj _ (evalOne_mem_fixed S _)
    have h1 := LinearMap.congr_fun h0 (levelZero π γ y0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs] at h1
    exact h1
  · intro p x
    have h3 := evalOne_parab hPF hΦ S p (sec x)
    calc (Φ ∘ₗ (evalOne S ∘ₗ sec)) (levelZero π p x)
        = Φ (evalOne S (levelZero S.toRepresentation p (sec x))) :=
          congrArg (fun w => Φ (evalOne S w)) (hs _ _)
      _ = _ := h3

end SlopeTestRemainingChoices

end UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Gal.InertialTypesAlt.SubquotientMaps in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.subqMap :
    FinSec → UpperTheory.Gal.TypesAndIwahori.ParaFactor → SubqMap := by
  intro hSec hPF k _ _ _ _ N s d hd W V Z _ _ _ _ _ _ ρ π κ Φ hΦ hinj hsq hfix
  obtain ⟨S, f, hf⟩ := hsq
  have : Finite (GL (Fin N) 𝓀[k]) := inferInstance
  obtain ⟨sec, hs, hfs⟩ := hSec (GL (Fin N) 𝓀[k])
    (fixed S.toRepresentation (KOne k (Fin N))) (fixed π (KOne k (Fin N)))
    (levelZero S.toRepresentation) (levelZero π) (levelZeroMap f).toLinearMap
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _ (levelZeroMap f) g x) (levelZeroMap_surjective f hf)
  exact main hPF hΦ hinj S sec hs (Function.LeftInverse.injective hfs) hfix
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppAny
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_block (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) {s N : ℕ} (d c : Fin s → ℕ) (hd : ∑ a, d a = N) (y : ℂ) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) =
      ∏ a, (X - C (y ^ c a)) ^ d a := by
  show (Finset.univ.val.map fun j => (fun a => (X - C (y ^ c a) : ℂ[X])) (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)).prod = _
  rw [hBC ℂ[X] N s d hd (fun a => X - C (y ^ c a)), Multiset.prod_sum]
  simp [Multiset.prod_replicate]

private theorem pol_top (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) (hPT : PolTop) (b : Lbl) {s N : ℕ} (d c : Fin s → ℕ)
    (hd : ∑ a, d a = N) (hl : List.ofFn (fun a => (d a, c a)) = b.D ++ b.L) (y : ℂ) (h2 : 2 ≤ b.q)
    (h1 : ∀ p ∈ b.L, p.1 = 1) (hy : y ^ (b.q - 1) = 1) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) = b.pol b.q y := by
  rw [prod_block hBC, (hPT b y h2 h1 hy).2, ← hl, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem pol_bot (hPB : PolBot) (q Q : ℕ) {s : ℕ} (m c : Fin s → ℕ) (y : ℂ) (h2 : 2 ≤ Q) (hy : y ^ (Q - 1) = 1) :
    (⟨q, [], List.ofFn fun a => (m a, c a)⟩ : Lbl).pol Q y =
      ∏ a, ∏ j ∈ Finset.range (m a), (X - C (y ^ (c a * q ^ j * ((Q - 1) / (q ^ m a - 1))))) := by
  rw [hPB q Q _ y h2 hy, List.map_ofFn, List.prod_ofFn]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.suppAny :
    (LblOn fun a => a.D = []) → LblOf → TypeOfLbl → UpperTheory.Gal.TypesAndIwahori.SuppOfType → UpperTheory.Gal.TypesAndIwahori.BlockCount → TameChars → LeTop → PolTop → PolBot → ResEmbEx → UnifTower → BaseQ → CardRes → ArtRead → CuspIne → SuppIne → SuppAny := by
  intro hOn hOf hTy hSO hBC hTC hLT hPT hPB hRE hUT hBQ hCR hAR hCI hSI
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  haveI : CharZero (v.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w.adicCompletion Y.K) := charZero_of_injective_algebraMap (algebraMap Y.K _).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hRE E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hRE Y.K Ω A w h'
  have eqv : τ.ρ.Equiv (IrrGL.of τ.ρ τ.smooth τ.irred).rep := IrrGL.equivOf _ _ _
  obtain ⟨𝔪, hm⟩ := UpperTheory.Zero.LLC.Pr.exh (v.adicCompletion E) (IrrGL.of τ.ρ τ.smooth τ.irred)
  have hS₀ : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) :=
    hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ hm
  have hS : HasSupport τ.ρ (msupp 𝔪) := hS₀.of_equiv eqv.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ := GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv eqv.symm hD
  have hθ : Inj (Θ.comp e.toMonoidHom) := fun a b ha hb hab =>
    e.injective (hΘ _ _ (by simpa using ha) (by simpa using hb) hab)
  obtain ⟨hg2, hcard, -⟩ := hBQ E v g i hi
  obtain ⟨s, x, c, hxS, hx, hlbl⟩ := hOf _ (Θ.comp e.toMonoidHom) hθ n _ τ.ρ _ hS hfix
  rw [hcard] at hlbl hx
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' _ rfl hlbl
  have hbq : b.q = g ^ f := by rw [hb.2.1, hCR, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · simp [hbq] at hb2
    · exact h0
  have hdiv : ∀ a, (x a).1 ∣ f := fun a =>
    hs _ hS _ (by rw [← hxS]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a))
  have hsp : (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).Splits b.q := by
    refine ⟨f, hf0, hbq, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hp
    exact hdiv a
  obtain ⟨-, -, hL1, hblk⟩ := hLT _ b hlbl.1 hab hsp
  obtain ⟨s', d, c', hd, ω, hl, hω, hTV⟩ := hTy _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hTS := hSO _ n s' d hd _ τ'.ρ τ'.smooth τ'.irred ω hTV
  obtain ⟨ξ, hξ, hξt, hξs, hξu⟩ := hTC _ n _ τ'.ρ _ hTS
  refine ⟨ξ, hξ, hξt, hξs, ?_⟩
  intro rc hrc a' ha' t
  have hQ : 1 ≤ normV w - 1 := by rw [hf, ← hbq]; omega
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Ω, ϖ ^ (normV w - 1) = (g : Ω) := IsAlgClosed.exists_pow_nat_eq _ hQ
  have hg1 : ((g : ℕ) : 𝓞 Y.K) ∈ w.asIdeal := DiscreteGroups.sglob.DzType.natCast_mem_of_normV w g f hf0 hf
  have hg2' : ((g : ℕ) : 𝓞 Y.K) ∉ w.asIdeal ^ 2 := hUT E Ω n (Pt.base Ω π) Y hY A hI v w h h' g hg2
  obtain ⟨z, u, hz, hu, hres, hpow⟩ := hAR Y.K Ω A w h' g hg1 hg2' a' ha' e' he' t ϖ hϖ
  obtain ⟨y, hyd⟩ : ∃ y : ℂ, y = Θ (IsLocalRing.residue A z) := ⟨_, rfl⟩
  have hy : y ^ (g ^ f - 1) = 1 := by rw [hyd, ← map_pow, ← hf, hpow, map_one]
  have hξ' : ∀ j, ((ξ j (a' (ineIncl h' t)) : ℂˣ) : ℂ) = y ^ c' (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j) := by
    intro j
    rw [← hu, hξu, hω, hyd, ← hres]
    rfl
  let t₀ : Ine (F := E) A := ⟨AlgEquiv.restrictScalars E (t : G Y.K Ω), t.2.1, t.2.2⟩
  have hcu : ∀ a, (rc (x a)).inePol (t₀ : G E Ω) =
      ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    intro a
    rw [hyd]
    exact hCI E Ω A v h g i hi Θ hΘ e (x a) (c a) (hx a).1 (hx a).2.1 (hx a).2.2.1 (hx a).2.2.2 rc hrc f hf0 (hdiv a)
      t₀ ϖ (hf ▸ hϖ) z hz
  have hSx : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) := hS₀
  have h1 := hSI E Ω A v h rc hrc _ _ hSx t₀
  rw [← hxS, Multiset.map_map] at h1
  have h2 : (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).inePol (t₀ : G E Ω) =
      ∏ a, ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    rw [h1, ← Finset.prod_congr rfl fun a _ => hcu a]
    rfl
  have h3 := pol_top hBC hPT b d c' hd hl y hb2 hL1 (hbq ▸ hy)
  have h4 := pol_bot hPB g (g ^ f) (fun a => (x a).1) c y (hbq ▸ hb2) hy
  have h5 : b.pol (g ^ f) y = (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).pol (g ^ f) y := by
    rw [← hbq]
    unfold Lbl.pol
    rw [hblk]
  rw [hbq, h5, h4] at h3
  simp only [hξ']
  exact h2.trans h3.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSuppIne
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

open UpperTheory.Zero.LLC in
private theorem charPol_seg' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT (h := h) a ha rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, L.nu]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

open UpperTheory.Zero.LLC in
private theorem charPol_supp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT (h := h) a ha rc) (x : IrrGL (k := w.adicCompletion E))
    (S : Multiset (IrrGL (k := w.adicCompletion E))) (hS : HasSupport x.rep S) (σ : Weil h) :
    (rc x).charPol σ = (S.map fun y => (rc y).charPol σ).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := Pr.exh (w.adicCompletion E) x
  have hs : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL Pr.zel _ 𝔪 x hm
  obtain rfl := (goodSeg (w.adicCompletion E)).2.2 x _ _ hS hs
  rw [L.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => charPol_seg' L Δ σ)

end UpperTheory.Gal.InertialTypesAlt

theorem UpperTheory.Gal.InertialTypesAlt.suppIne :
    SuppIne := by
  intro E Ω _ _ _ _ _ A v h rc hrc x S hS t
  obtain ⟨a, ha, L⟩ := hrc
  rw [WD.inePol_of_mem_Ine _ t.2,
    Multiset.map_congr rfl fun y _ => WD.inePol_of_mem_Ine (rc y) t.2]
  exact UpperTheory.Gal.InertialTypesAlt.charPol_supp L x S hS _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameChars
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.tameChars :
    TameChars := by
  intro k _ _ _ _ N V _ _ π ω h
  obtain ⟨μ, hμ, H⟩ := h
  have hs : ∀ j, IsSmoothChar (μ j) := fun j => isSmoothChar_of_isTame (hμ j).isTame
  refine ⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩
  · exact (hμ j).isTame u hu
  · have := hasSupport_of_isCuspSupport H
    exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTensTr
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_map_eq_prod {s : ℕ} {W : Fin s → Type} [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] [∀ a, FiniteDimensional ℂ (W a)] (f : ∀ a, W a →ₗ[ℂ] W a) :
    LinearMap.trace ℂ (PiTensorProduct ℂ W) (PiTensorProduct.map f) =
      ∏ a, LinearMap.trace ℂ (W a) (f a) := by
  let b := fun a => Module.finBasis ℂ (W a)
  let B := Basis.piTensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ a, LinearMap.trace ℂ (W a) (f a) = ∑ j, (b a).repr (f a (b a j)) j := by
    intro a
    rw [LinearMap.trace_eq_matrix_trace ℂ (b a), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem UpperTheory.Gal.InertialTypesAlt.tensTr :
    TensTr := by
  intro s Γ W _ _ _ _ κ
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun a => Module.finBasis ℂ (W a)), fun x => ?_⟩
  exact trace_map_eq_prod fun a => κ a (x a)
end

