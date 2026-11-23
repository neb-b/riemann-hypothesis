module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstPairPadicComplexOfConstantCoeffZero
section
noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

section Frob

variable {σ : ℂ_[l] →+* ℂ_[l]}

end Frob

end GlobalTheory.ThBe0.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRham
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AbsIrrConstituents

theorem mapRep_comp {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep (g.comp f) ρ = mapRep g (mapRep f ρ) := by
  ext x i j
  rfl

theorem fixedJumps_nodup (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* Qbar (D.nd.l i)) :
    (D.naut.locAutHodgeTateWeightsLevelZero i τ).Nodup := by
  have h1 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
  rw [D.nbc.embAV_inf i P] at h1
  have h2 := (D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1
  have h3 := h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)
  rw [← h1] at h3
  exact h3.of_map _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem mem_of_induces' (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  apply (h _).mp
  have e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp only [map_natCast]
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem sumRep_coe {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix _ _ k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem coe_mapRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (ρ g : Matrix (Fin a) (Fin a) k).map f := rfl

theorem mapRep_sumRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a b : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) :
    mapRep f (SumRepresentations.At.sumRep ρ ρ') = SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext g i j
  rw [coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem contQ_sumRep (D : D7) (i : D.nd.Loc) {a b : ℕ}
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (h : SumRepresentations.At.ContQ D.nd i ρ) (h' : SumRepresentations.At.ContQ D.nd i ρ') : SumRepresentations.At.ContQ D.nd i (SumRepresentations.At.sumRep ρ ρ') := by
  unfold SumRepresentations.At.ContQ at *
  simp only [sumRep_coe, Matrix.reindex_apply]
  exact (Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem rel_map' {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {a d u : ℕ} (h : d + d + u = a)
    (ρ : Γ →* GL (Fin a) k) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix _ _ k)) :
    ∀ g, (((Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm)⁻¹ *
        mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm :
          GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.reindex (finCongr h) (finCongr h)
        ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep (mapRep f σ) (mapRep f σ)) (mapRep f υ) g : GL (Fin (d + d + u)) L) :
          Matrix _ _ L) := by
  subst h
  intro g
  have e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ *
      mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm =
      Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* Matrix _ _ L).toMonoidHom
        (Pm⁻¹ * ρ g * Pm) := by
    simp only [map_mul, map_inv]; rfl
  rw [e1]
  show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _
  rw [hrel g]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  rw [← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]

theorem jumps_not_nodup' (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hτ : InducesW D.nd i τ w)
    (hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i))
    {a d u : ℕ} (h : d + d + u = a) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) (Qbar (D.nd.l i)))
    (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) (Qbar (D.nd.l i))) (Pm : GL (Fin a) (Qbar (D.nd.l i)))
    (hd : 0 < d) (hc : SumRepresentations.At.ContQ D.nd i ρ) (hcσ : SumRepresentations.At.ContQ D.nd i σ) (hcυ : SumRepresentations.At.ContQ D.nd i υ)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) (Qbar (D.nd.l i))) :
            Matrix _ _ (Qbar (D.nd.l i))))
    (hdR : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w') :
    ¬ (D.naut.jumpsW i ρ τ).Nodup := by
  intro hnd
  subst h
  obtain ⟨-, -, hJC, hG⟩ := ht.2.2
  obtain ⟨-, hconj, hsum, -⟩ := hG i
  have hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm := by
    intro g; ext1; rw [hrel g]; simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hcA := contQ_sumRep D i σ σ hcσ hcσ
  obtain ⟨hdRc, -, hJc⟩ := hconj _ ρ _ hc Pm hPm
  obtain ⟨hdRs, -, hJs⟩ := hsum _ _ _ υ hcA hcυ
  obtain ⟨hdRσ, -, hJσ⟩ := hsum _ _ σ σ hcσ hcσ
  have hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w' :=
    fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')
  have hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w' :=
    fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')
  have hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w' :=
    fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1
  have e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ := by
    rw [← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']
  have hcard := hJC i _ σ w τ hw hτ (hdRσ' w hτ).1
  rw [e] at hnd
  have h2 := (Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2
  obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)
  exact Multiset.disjoint_left.1 h2 hj hj

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

theorem continuous_blocks' {k Γ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Group Γ]
    [TopologicalSpace Γ] {a b c : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ₁ : Γ →* GL (Fin b) k)
    (ρ₂ : Γ →* GL (Fin c) k) (h : b + c = a) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) :
    (Continuous fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) ∧
      Continuous fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k) := by
  subst h
  have hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) := by
    have e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g =>
        ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k) := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, hrel g]
      simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  constructor
  · have e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _
  · have e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

end GlobalTheory.AbsIrrConstituents
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.integral_jets_realPlace_local_bases

theorem tauEmb_ringHom (D : D7) {p : ℕ} [Fact p.Prime] (lm : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ g : D.host.E →+* ℂ_[p], ∀ x, tauEmb D lm τ x = g x := by
  have hm : ∀ x, embT D τ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  exact ⟨lm.comp ((embT D τ).codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

theorem jetsIntegral_basR : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  intro D cD hD N N' L L' hA p _ lm B B' κ hB hB' hκ F hF
  refine (GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames D N N' p lm (YYl D L L') F).2 hF _ _ ?_
  rintro ⟨j1, a, b⟩
  by_cases h0 : lamC lm (cD (tauPl D j1)) = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun ⟨τ, k1, k2⟩ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs with h
    · subst h
      have : κ (tauPl D j1) = 0 := by
        have := hκ (tauPl D j1); rw [h0, norm_zero] at this; exact norm_le_zero_iff.1 this
      simp [this]
    · rfl
  · set τ0 := tauPl D j1 with hτ0
    set c := κ τ0 / lamC lm (cD τ0) with hc
    have hcn : ‖c‖ ≤ 1 := by
      rw [hc, norm_div]; exact div_le_one_of_le₀ (hκ τ0) (norm_nonneg _)
    obtain ⟨n, r, aa, hr, haa, hsum⟩ := GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hD p lm τ0
    obtain ⟨m, r', A, hr', hA', hAsum⟩ :=
      _root_.GlobalTheory.EntryHomComb.entry_comb D N N' L L' hA p lm τ0 (B τ0) (B' τ0) (hB τ0) (hB' τ0) a b
    refine ⟨n * m, fun t => c * r (finProdFinEquiv.symm t).1 * r' (finProdFinEquiv.symm t).2,
      fun t => aa (finProdFinEquiv.symm t).1 • A (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
    · intro t
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖r _‖ * ‖r' _‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hr _
            · exact hr' _
        _ = 1 := by norm_num
    · intro t
      exact Submodule.subset_span ⟨aa _, haa _, A _, hA' _, rfl⟩
    · rintro ⟨τ, k1, k2⟩
      obtain ⟨g, hg⟩ := tauEmb_ringHom D lm τ
      rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      have key : ∑ i : Fin n, ∑ j : Fin m, c * r i * r' j * tauEmb D lm τ ((aa i • A j) k1 k2)
          = c * ((∑ i, r i * tauEmb D lm τ (aa i)) * (∑ j, r' j * tauEmb D lm τ (A j k1 k2))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, Matrix.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [key, hsum τ]
      split_ifs with h1 h2 h2
      · subst h2
        rw [← hAsum k1 k2, hc, ← mul_assoc, div_mul_cancel₀ _ h0, mul_assoc]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
end GlobalTheory.Proof.integral_jets_realPlace_local_bases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

namespace GlobalTheory.CurveToStdLog

open MvPowerSeries

variable {l : ℕ} [Fact l.Prime] {κ κ' : Type}

theorem mvsubst_subst {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a) {b : MvPowerSeries κ ℂ_[l]}
    (hb : constantCoeff b = 0) (f : PowerSeries ℂ_[l]) :
    MvPowerSeries.subst a (f.subst b : MvPowerSeries κ ℂ_[l]) = f.subst (MvPowerSeries.subst a b) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]
  rfl

theorem subst_expMv [Finite κ] {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : ∀ i, constantCoeff (a i) = 0)
    {f : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf,
    GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]

theorem expMv_add {f g : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expMv (f + g) = expMv f * expMv g := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
    GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expMv_zero : expMv (0 : MvPowerSeries κ ℂ_[l]) = 1 := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero

theorem expMv_sum {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries κ ℂ_[l]}
    (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expMv_zero
  | insert i s hi ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]

theorem cc_ph (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) :
    PowerSeries.constantCoeff g.ph = 0 := by
  have h := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1
  show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
  rw [map_neg, h, neg_zero]

theorem cc_phAt (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) : constantCoeff (g.phAt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)

theorem inv_ePhi1 (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
  have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
  have h := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2
  rw [subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one,
    coe_substAlgHom] at h
  have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
  exact h

end GlobalTheory.CurveToStdLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem isHeckeGaloisQ_of_isHeckeGalois : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  intro D i x r hr
  refine ⟨SumRepresentations.contQ_of_continuous D.nd D.naut i r hr.1, ?_, ?_⟩
  · have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ hr.2.1
    have e : mapRep (iotaOQ D.nd D.naut i) r =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r) := by
      ext g a b
      rfl
    rw [e]
    exact h
  · intro w hw B σ hB hσ
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e3, Matrix.charpoly_map, hr.2.2 w hw B σ hB hσ]

end GlobalTheory.NRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
section
noncomputable section

namespace GlobalTheory.OnePlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem GlobalTheory.TwU

def xiE {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) :
    Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]
  | Sum.inl (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inl r))
  | Sum.inr (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inr r))

def jetZ (p : ℕ) [Fact p.Prime] (n' r0 r1 : ℕ) (z : Zidx n' r0 r1) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p] :=
  jetLogG p n' (((z.1 : ℕ) : ZMod n'), z.2)

end GlobalTheory.OnePlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJets
section
noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def StdAt (D : D7) (g : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) ∧ EqAt D g L L₀


end GlobalTheory.LiftTypePrime

end
end

