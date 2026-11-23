module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PZetaLoc
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

private theorem map_scalar' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin a) y) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map f.toMonoidHom y) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, h]

section

open GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem pInf_quo (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map (pInf E).toMonoidHom (quo E (localIdele E w u)) = 1 := by
  have h1 : pInf E ((localIdele E w u : Ideles E) : Ad E) = 1 := by
    change (infEq E).symm (1 : InfiniteAdeleRing E) = 1
    exact map_one _
  have h2 : Units.map (pInf E).toMonoidHom (localIdele E w u) = 1 := Units.ext h1
  have h3 : Units.map (pInf E).toMonoidHom (cj E (localIdele E w u)) = 1 := by
    refine Units.ext ?_
    change pInf E (conjAd E ((localIdele E w u : Ideles E) : Ad E)) = 1
    rw [GlobalTheory.CompanionTheory.OnlyStab.pInf_conj, h1, map_one]
  rw [quo_apply, _root_.map_div, h2, h3, div_one]

private theorem loc_quo (w v : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u)) =
      Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) /
        Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) := by
  rw [quo_apply, _root_.map_div]

private theorem loc_id_ne {w v : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) = 1 :=
  Units.ext ((Neutral.B1.localIdele_isSupportedAt E w u).2 v h)

private theorem loc_cj_ne {w v : HeightOneSpectrum (𝓞 E)} (h : conjSrc (conjE E) v ≠ w)
    (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) = 1 := by
  refine Units.ext ?_
  change conjLoc (conjE E) v (((localIdele E w u : Ideles E) : Ad E).2 (conjSrc (conjE E) v)) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt E w u).2 _ h, map_one]

private theorem loc_id_self (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E w).comp (pFin E)).toMonoidHom (localIdele E w u) = u :=
  Units.ext (Neutral.B1.localIdele_snd_self E w u)

end

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.zetaLoc_of :
    ZetaLoc := by
  intro E _ _ _ a ζ hζ w hw u
  obtain ⟨hne, hund, -⟩ := over_split hw
  have hc : ∀ v, cLoc v (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a)
      (Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u))) := by
    intro v
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar']
  have hi : cInf (ζ (localIdele E w u)) = 1 := by
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar', pInf_quo, map_one]
  refine ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hi, Subgroup.mem_iInf.2 fun v =>
    Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_⟩, ?_⟩
  · have h1 : v ≠ w := fun e => hv (by rw [e])
    have h2 : conjSrc (conjE E) v ≠ w := fun e => hv (by
      rw [← hund, ← e, conjSrc_conjSrc_cm])
    rw [hc, loc_quo, loc_id_ne h1, loc_cj_ne h2, div_one, map_one]
  · rw [hc, loc_quo, loc_id_self, loc_cj_ne hne, div_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.SeedFinOddOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Geo (GeoOne)

namespace UpperTheory.Gal.Int.Div

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem apart_cpl {w u : HeightOneSpectrum (𝓞 E)} (hu : IsSplitAt u) : Apart w (cpl u) ↔ Apart w u := by
  unfold Apart
  rw [(GlobalTheory.SplitPts.over_split hu).2.1]

private theorem apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) : Apart u w := Ne.symm h

private theorem mem_cpl (hC : CplMem) {l : ℕ} {u : HeightOneSpectrum (𝓞 E)} (h : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    ((l : ℕ) : 𝓞 E) ∈ (cpl u).asIdeal := (hC E u l l (by simp)).2 h

private theorem move (hC : CplMem) (hS : SameOr) {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E} (hx : x ^ 2 = -(d : E))
    {u w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt u) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {p : HeightOneSpectrum (𝓞 E) → Prop} (h1 : p u) (h2 : p (cpl u)) :
    ∃ u', ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal ∧ SameK x u' w ∧ p u' ∧ ∀ y, Apart y u' ↔ Apart y u := by
  rcases hS E l d hl hd x hx u w hu hw with h | h
  · exact ⟨u, hu, h, h1, fun _ => Iff.rfl⟩
  · exact ⟨cpl u, mem_cpl hC hu, h, h2, fun _ => apart_cpl hs⟩

end

theorem seedFinOdd_of (hD : DivAll) (hC : CplMem) (hS : SameOr) (hSat : SatConj) (hTy : TyConj) (hLac : LacConj) (hGap : GapLac)
    (hGen : DGenMul) (hG : GeoOne) : SeedFinOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha hodd d hd T hT w₀ v' hw₀ hs₀ hv' hs' hap U₀ S Y
  refine ⟨∅, by simp, fun U hA hty hwt hsph hsv _ => ?_⟩
  obtain ⟨hd0, x, hx⟩ := hd.1
  have hlac : LacWtAt ι v' U := by
    obtain ⟨-, τ, hτ, h⟩ := hwt
    obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hA.1
    exact ⟨τ, hτ, lam τ, hlam τ, hGap a _ (card_wtJumps _) (h _ (hlam τ) _ (wtJumps_val _))⟩
  have geo : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ u₀ u', SameK x w u' ∧ (∀ y, Apart y u₀ ↔ Apart y w₀) ∧
      (∀ y, Apart y u' ↔ Apart y v') ∧ _ := fun w hw => by
    obtain ⟨u₀, a1, a2, a3, a4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs₀ hw₀ hw
      (p := fun u => GlobalTheory.CongW.TyEll E l a u U) hty (hTy E l a U w₀ hs₀ hty)
    obtain ⟨u', b1, b2, b3, b4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs' hv' hw
      (p := fun u => (∃ B, SatU U u B) ∧ LacWtAt ι u U) ⟨hsv, hlac⟩ ⟨hSat E a U hA.1 v' hs' hsv, hLac E l ι a ha U v' hlac⟩
    exact ⟨u₀, u', fun y hy => (b2 y hy).symm, a4, b4, hG E Ω l ι a hodd d hd x hx T hT u₀ u' a1 b1
      ((a4 u').2 (apart_symm ((b4 w₀).2 (apart_symm hap)))) (fun y hy => (a2 y hy).trans (b2 y hy).symm) S U hA a3
      (fun y h1 h2 h3 => hsph y h1 ((a4 y).1 h2) h3) b3.1 b3.2⟩
  obtain ⟨_, _, -, -, -, g1, g2, -⟩ := geo v' hv'
  obtain ⟨r, ⟨r1, r2, V, X, v1, v2, v3⟩, hr⟩ := hD E Ω l ι a ha d hd.1 U hA.1 g1
  have hgm : ∀ w B, SatU U w B → GlobalTheory.CongW.GenOf DGen a (normV w) B → GenericMul B := fun w B hB hg =>
    hGen a _ B ha hB.choose_spec.2.card hg
  have hsp : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw => by
    by_contra h
    exact (hd.2.2.2 w h).1 hw
  refine ⟨r, r1, r2, ⟨V, X, v1, v2, fun w h1 h2 h3 _ => v3 w h1 h2 h3⟩, fun w _ h1 h2 _ B hB hg => ?_,
    fun w _ h1 h2 h3 h4 => ?_, fun w _ h1 h2 h3 _ B hB hg => ?_⟩
  · obtain ⟨dd, ρ, k1, k2⟩ := g2 w h1 h2 ⟨B, hB⟩
    exact (hr dd ρ k1 w).1 h1.1 h2 B hB (hgm w B hB hg) (k2 B hB)
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨⟨dd, ρ, k1, k2, k3⟩, -⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) (hsph w (hsp w h1) h2 h4)
    exact (hr dd ρ k1 w).2.1 k2 k3
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨-, dd, ρ, k1, k2⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) ⟨B, hB⟩
    exact ((hr dd ρ k1 w).2.2 (hsp w h1) B hB (hgm w B hB hg) (k2 B hB)).2.phiAt

end UpperTheory.Gal.Int.Div

end
end

