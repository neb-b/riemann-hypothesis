module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FullLevelAction

open GlobalTheory.LevelActionLaws

theorem actLaws_levFull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) :
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (y y' : FrPt Xo c S) =>
        levActR (Xo := Xo) (c := c) (levFull Dw l) g' y y') := by
  obtain ⟨⟨ι, hι, hone⟩, hmul, hnb⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨ρ, ν, i, h⟩ := exists_move hpq hA Xo g
    obtain ⟨y', hy'⟩ := (_root_.GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν h.1 S y).1
    exact ⟨y', ρ, ν, i, h, hy'⟩
  · intro g S _ _ y y' y'' h' h''
    obtain ⟨ρ, ν, i, h, hm⟩ := h'
    have hm' := frMove_transfer hpq hA Xo c g i h h''
    obtain rfl := (_root_.GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y').2.1
  · intro S _ _ y
    refine ⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (eta_congr Xo (liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  · intro g g' S _ _ y y' y'' h h'
    obtain ⟨ρ, ν, i, h, hm⟩ := h
    obtain ⟨ρ', ν', i', h', hm'⟩ := h'
    obtain ⟨μ, hμ, hc⟩ := hmul ρ ρ' ν ν'
    refine ⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hm hm'⟩
    · rw [Category.assoc, h'.1, h.1]
    · have e : Xo.univ.eta ((levFull Dw l (g * g')).1 a) =
          Xo.univ.eta ((levFull Dw l g).1 ((levFull Dw l g').1 a)) :=
        eta_congr Xo (liftLa_mul_sub g g' a)
      rw [e, hμ, ← Category.assoc, h.2.1, Category.assoc, h'.2.1, Category.assoc]
    · have e : (levFull Dw l (g * g')).2 a = (levFull Dw l g).2 ((levFull Dw l g').2 a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  · intro g S T _ _ _ _ φ y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)
  · intro g S _ _ t y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)

theorem actLev_levFull : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  intro D Q j hpq hA
  exact actLaws_levFull (Q.Xo j) Q.c hpq (by rw [hA]; exact Nat.coprime_one_left _)

end GlobalTheory.FullLevelAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.AlphaForm

theorem totalDegree_harm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq] at hP
  obtain ⟨⟨-, -, hD⟩, -⟩ := hP
  have hR : ∀ m ∈ P.support, (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine (Fintype.sum_sigma (fun ℓ => m ℓ)).trans ?_
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hD m hm τ i
  apply le_antisymm
  · exact Finset.sup_le fun m hm => (hR m hm).le
  · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
    rw [← hR m hm]
    exact MvPolynomial.le_totalDegree hm

theorem nrm_mul_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {l : Level H}
    (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α β : 𝓞 E) (N : ℕ) (h : α * β = (N : 𝓞 E)) :
    nrm Dw c a α * nrm Dw c a β = (N : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) := by
  simp only [nrm]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← mul_pow, ← map_mul, h, map_natCast]

theorem alphaForm_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (α : 𝓞 E), α * star α = (l.M : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (n : ℕ) (b : Fin n → (ptO Xo yF.x ⟶ Xo.univ.t.G)) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo yF.x))), (∀ i, b i ≫ Xo.univ.t.act.act (star α) = 1) → (∀ i, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M yF.s (b i) (hh i)) → ∃ (xx : Fin n → Dw.La) (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x))), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (l.M : ℤ) (hh i) (colOf m i) = algebraMap c.F F (nrm Dw c a α) * thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab F _ _ _ yF α hα hMb n b hh hb hT
  letI := H.starRing
  have hI := fun i => GlobalTheory.T.normalizedPullback_conjugate_translate_eq_translate_level E H Dw l Xo c F yF.x α hα hMb yF.s (b i) (hh i) (hb i) (hT i)
  choose Fs hN hV using hI
  have hK : ∀ i, KilledBy Xo l.Mb (b i ≫ Xo.univ.t.act.act α) := by
    intro i
    unfold KilledBy
    intro x hx
    rw [hMb, Ideal.mem_span_singleton'] at hx
    obtain ⟨r, rfl⟩ := hx
    have e : α * (r * star α) = star α * (α * r) := by ring
    rw [Category.assoc, ← Xo.univ.t.act.mul, e, Xo.univ.t.act.mul, ← Category.assoc, hb i]
    haveI := Xo.univ.t.act.hom (α * r)
    simp
  choose xx hxx using fun i => GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel E H Dw l Xo c F yF (b i ≫ Xo.univ.t.act.act α) (hK i)
  refine ⟨xx, Fs, fun i => by rw [hxx i]; exact hV i, ?_⟩
  intro a Pp hPp
  have hs : star α * star (star α) = ((l.M : ℕ) : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hα
  have hz : ((l.M : ℤ) ^ 2) = ((l.M * l.M : ℕ) : ℤ) := by push_cast; ring
  have h := GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab F yF (star α) l.M l.M ((l.M : ℤ) ^ 2) hs hz n hh Fs hN a Pp hPp
  have hM : ((l.M : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  unfold thExpr
  rw [h]
  by_cases h0 : Pp = 0
  · subst h0
    simp
  have key : nrm Dw c a α * ((l.M : c.F) ^ Pp.totalDegree)⁻¹ * nrm Dw c a (star α) = 1 := by
    rw [totalDegree_harm c hPp h0, _root_.mul_right_comm, nrm_mul_nrm Dw c a α (star α) l.M hα]
    exact mul_inv_cancel₀ (pow_ne_zero _ hM)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← map_mul, ← map_mul, key, map_one, _root_.one_mul]

end GlobalTheory.AlphaForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSimInducing
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical

namespace GlobalTheory.CoverCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sup_eq_top_of_level (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p)
    (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) : l.Mb ⊔ I = ⊤ := by
  have h0 : (Ideal.span {(l.M : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    have := l.three_le
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    omega
  have h1 : Ideal.span {(l.M : 𝓞 E)} * (I * I.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {(p : 𝓞 E)} := by
    have h := l₂.prod
    rw [hI, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h
    rw [← h, ← l.prod]
    ring
  have h2 := mul_left_cancel₀ h0 h1
  have hpI : (p : 𝓞 E) ∈ I := by
    have : (p : 𝓞 E) ∈ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [h2]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hp).map (Int.castRingHom (𝓞 E))
  rw [Ideal.eq_top_iff_one, ← huv]
  refine Ideal.add_mem _ (Ideal.mem_sup_right (I.mul_mem_left _ ?_)) (Ideal.mem_sup_left (l.Mb.mul_mem_left _ ?_))
  · simpa using hpI
  · simpa using hMM

theorem exists_sim_inducing (D : Datum H) (hpq : 1 ≤ D.p + D.q) (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E))
    (hd : l.Dvd l₂) (hM : l₂.M = l.M * p) (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) (hA : l₂.A = 1)
    (k : (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) ≃ₗ[𝓞 E] (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La))) :
    ∃ g : Sim D, g.InGam l l₂ ∧
      ∀ a : D.La, (Submodule.Quotient.mk (g.f l₂.M a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
        k (Submodule.Quotient.mk a) := by
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ l.Mb ⊔ I by rw [sup_eq_top_of_level l l₂ p I hM hp hI]; trivial)
  haveI : Module.Projective (𝓞 E) D.La := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • ⊤ : Submodule (𝓞 E) D.La).mkQ
    (k.toLinearMap ∘ₗ (I • ⊤ : Submodule (𝓞 E) D.La).mkQ) (Submodule.mkQ_surjective _)
  have hf' : ∀ a, (Submodule.Quotient.mk (f a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
      k (Submodule.Quotient.mk a) := fun a => LinearMap.congr_fun hf a
  set F : D.La →ₗ[𝓞 E] D.La := e • f + e' • LinearMap.id with hF
  have h1 : ∀ x, F x - f x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - f x = e' • (x - f x) := by
      have h : e = 1 - e' := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he' Submodule.mem_top
  have h2 : ∀ x, F x - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - x = e • (f x - x) := by
      have h : e' = 1 - e := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he Submodule.mem_top
  have lM : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ l.Mb • ⊤ := Submodule.smul_mono_left hd.2.1
  have lI : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ I • ⊤ :=
    Submodule.smul_mono_left (by rw [hI]; exact Ideal.mul_le_inf.trans inf_le_right)
  obtain ⟨g, g1, -⟩ := GlobalTheory.exists_sim_of_aut_mod E H D l₂ 1 F hpq one_pos (Nat.coprime_one_left _) (by
    intro x hx
    have x1 : x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lM hx) (h2 x)
      rwa [sub_sub_cancel] at this
    have x2 : x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lI hx) (h1 x)
      rw [sub_sub_cancel, ← Submodule.Quotient.mk_eq_zero, hf', k.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
    have : x = e • x + e' • x := by rw [← add_smul, hee, one_smul]
    rw [this, hI]
    refine Submodule.add_mem _ ?_ ?_
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he x2
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul he' x1)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : 0 < p := by
    have := l₂.three_le
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [hM, h] at this; omega
    · exact h
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hA1 : l.A = 1 := Nat.dvd_one.1 (hA ▸ hd.2.2)
  refine ⟨g, ⟨by rw [hA]; simp, fun a => ?_, fun a => ⟨g.f l.A a - a, by rw [hA1, one_smul]⟩⟩, fun a => ?_⟩
  · obtain ⟨b, hb⟩ := g.tower l.M p hM0 hp0 a
    rw [← hM] at hb
    have h3 : g.f l₂.M a - g.f l.M a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      rw [hb, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMM Submodule.mem_top
    have := Submodule.sub_mem _ (Submodule.add_mem _ (lM (g1 a)) (h2 a)) h3
    convert this using 1
    abel
  · rw [← hf', Submodule.Quotient.eq]
    have := Submodule.add_mem _ (lI (g1 a)) (h1 a)
    rwa [sub_add_sub_cancel] at this

theorem psi_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k], Nonempty (FrPt d.Xo₂ d.c₂ k) → ∀ ψ ψ' : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, d.PsiTie ψ → d.PsiTie ψ' → ψ = ψ' := by
  intro E _ _ _ H Dw l Xo c n d hpq hlev hA K _ _ _ ⟨y⟩ ψ ψ' h h'
  obtain ⟨hd, hM, hp, hI, -, -, -, -, hne⟩ := hlev
  ext k
  obtain ⟨g, hg, hk⟩ := exists_sim_inducing Dw hpq l d.l₂ d.pd d.I hd hM hp hI hA k
  obtain ⟨ρ, hρ⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq d.Xo₂ g hg.1
  obtain ⟨hs, ν, -⟩ := id hρ
  obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw d.l₂ d.Xo₂ d.c₂ ρ.hom ν hs K y).1
  have hgA : ∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a) := fun a => ⟨g.f d.l₂.A a - a, by rw [hA, one_smul]⟩
  have e1 := h k g ρ hg hgA hρ hk K y y' hy'.1
  have e2 := h' k g ρ hg hgA hρ hk K y y' hy'.1
  have e3 := mul_right_cancel₀ (hne K y) (e1.symm.trans e2)
  have e4 := d.eF.injective ((algebraMap d.c₂.F K).injective e3)
  rw [e4]

end GlobalTheory.CoverCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitOfPrimeNe
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorsAtPoint

theorem isUnit_of_prime_ne {V : Type} [CommRing V] [IsLocalRing V] {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime)
    (hne : g ≠ g') (hn : ¬ IsUnit ((g : ℕ) : V)) : IsUnit ((g' : ℕ) : V) := by
  have hz : IsCoprime (g : ℤ) (g' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hg hg').2 hne)
  obtain ⟨a, b, hab⟩ : IsCoprime ((g : ℕ) : V) ((g' : ℕ) : V) := by
    simpa using hz.map (Int.castRingHom V)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h₁ | h₁
  · exact absurd (isUnit_of_mul_isUnit_right h₁) hn
  · exact isUnit_of_mul_isUnit_right h₁

section Cast
variable {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem famCast_symm {k k' : ℕ} (e : k = k') (s : Fam Dp F k') : famCast e (famCast e.symm s) = s := by
  subst e; rfl

theorem famCast_sum {k k' : ℕ} (e : k = k') {m : ℕ} (a : Fin m → F) (b : Fin m → Fam Dp F k) :
    famCast e (∑ i, a i • b i) = ∑ i, a i • famCast e (b i) := by
  subst e; rfl

end Cast

theorem nuGe_famCast {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {Dd : DegData V (maximalIdeal V)} {Q : Dd.toPre.X → ℤ} {K : Type} [Field K] [Algebra (FractionRing V) K]
    {v : AddValuation K (WithTop ℚ)} {k k' : ℕ} (e : k = k') {s : Fam Dd.toPre K k} {r : ℚ}
    (h : NuGe Dd Q K v k s r) : NuGe Dd Q K v k' (famCast e s) r := by
  subst e; exact h

theorem unitBall_spanned (hL : Laws) (hT : TwistBaseChangeStatement)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [gr : GrpObj G'] [cm : IsCommMonObj G'] (U' : Unif (maximalIdeal V) D' A' G')
    [md : Module (𝓞 E) D'.toPre.X] :
    letI := H.starRing
    ∀ (oD' : D'.toPre.OAct (𝓞 E)) (oA' : A'.OAct (𝓞 E)) (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'),
      P'.TorsionIso → t'.G = G' → HEq t'.grp gr → HEq t'.comm cm → P'.D = D' → HEq P'.mod md → HEq P'.oD oD' →
      P'.A = A' → HEq P'.oA oA' → HEq P'.U U' →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : D'.toPre.X → ℤ), IsQ D'.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ A'.A) (fun a g => g ≫ oA'.act a)
        (fun n g g' c => WeilIs A'.A A'.L n g g' (unitOn c))),
    ∀ θ : Fam D'.toPre F 1, NuGe D' Q F v 1 θ 0 → ThFrame D' ϖ F θ →
    ∀ θα : Fam D'.toPre F (1 * N), PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ oA'.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro oD' oA' t' P' hP e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  exact ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws hL n1c (GlobalTheory.twisting_statements_of_laws hL hT).1
    (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H V t' P' hP

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → GenPointT := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hne hgo hg'o π π' hπ hπ' hcop hcop' hgnu F _ _ _ _ _ _ v hv I n
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hact s s₂ p w ζ x t₀ t σ' h hbox
  obtain ⟨hs, hs₂, ⟨hw, hζ, hfo⟩, hqx, hxk, hphi, hsm, hexp, hgerm⟩ := hbox
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hπb : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ
  have hπb' : star π' * star (star π') = (g' : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ'
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos hπb
  obtain ⟨pl₂, -, hpl₂⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π * star π') (g' * g) 1 hq
    le_rfl (by rw [star_mul', Nat.cast_mul, ← hπb, ← hπb']; ring)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n _ pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F
    (g' * g) hq
  obtain ⟨θ, θα, hθν, hθF, hθα⟩ := PowThetaFrame.main hL hL2 hL4 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
    hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  obtain ⟨oA', hoA, hQ', ⟨Dw', ⟨I'⟩⟩, t', P', hP', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    powPEL_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
      hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv I Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  have hcopb : ∃ u u' : 𝓞 E, u * star π' + u' * star (star π') = 1 := by
    obtain ⟨u, u', hu⟩ := hcop'
    exact ⟨u', u, by rw [star_star, ← hu]; ring⟩
  obtain ⟨m, pb, xb, wb, ζb, tb, a, hpx, hxb, hwb, htb, ha, hsum⟩ :=
    unitBall_spanned hL hT E H T.V D' A' G' U' oD' oA' t' P' hP' e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ (star π') g' hg'.pos hπb' hcopb
      (isUnit_of_prime_ne hg hg' hne hgnu) ϖ hϖ _ hQ' F v hv Dw' I' θ hθν hθF θα hθα
      (famCast (Dp := D'.toPre) (F := F) (one_mul g').symm s) (nuGe_famCast _ hs)
  have hs' : s = ∑ i, a i • famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i) := by
    rw [← famCast_sum, ← hsum, famCast_symm]
  let Λ : Fam D'.toPre F g' →ₗ[F] Fam D'.toPre F (g' * g) := (ζ • Φ) ∘ₗ pl
  refine ⟨θ, pl₂ θ, m, a, fun i => gm (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i))), hθν, hθF,
    (hpl₂ _ _).2 rfl, ha, ?_, fun i => ?_⟩
  · have ht : t = Λ s := by
      rw [(DVR.isSmul_iff _ _ _).1 hsm, (hΦ _ _).1 hphi, (hpl _ _).1 hs₂]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), ht, hs', map_sum, map_sum]
    simp only [map_smul]
  · obtain ⟨tb₀, h₁, h₂⟩ := htb i
    obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
      PowDescent.descentIdF_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
        hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact oA' hoA θ θα hθα
        (pb i) (wb i) (ζb i) (xb i) tb₀ (tb i) (hpx i) (hxb i) (hwb i).1 (hwb i).2.1 (hwb i).2.2 h₁ h₂
        p w ζ x hw hζ hfo hqx hxk _ _ (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
        ((hpl _ _).2 rfl) ((hΦ _ _).2 rfl) ((DVR.isSmul_iff _ _ _).2 rfl)
    obtain ⟨σ₂, j₁, j₂⟩ := hgmex (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
    refine ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, k₂, fun b => ?_, k₄, k₅, k₆, (hpl₂ _ _).1 k₁ ▸ k₇, k₈, k₉ ▸ j₁,
      (hiff F _ σ₂ _).2 j₂⟩
    have := pA.hom b
    rw [← hoA, ← Category.assoc, k₃, MonObj.one_comp]

end GlobalTheory.GeneratorsAtPoint
end
end

