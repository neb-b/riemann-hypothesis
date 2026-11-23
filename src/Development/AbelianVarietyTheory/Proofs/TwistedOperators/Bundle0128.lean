module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def VacAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) :
    Place D → (WO S T → ℂ) → Prop
  | .inl v => fun f => IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f
  | .inr τ => fun f => IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsLocOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ)
    (p : Place D) (x : WO S T → ℂ) : Prop :=
  ∃ L : (WO S T → ℂ) → ℂ, (∀ (c : ℂ) (φ : WO S T → ℂ), L (fun w => c * φ w) = c * L φ) ∧
    (∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 f' g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f) g) ∧
    ∀ g, IsThetaFunO ψ S T g → ipO μ 𝓕 x g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f₀) g


open Classical in
def pull {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v))
    (Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf a t then Φ (κ t) else 0

def IsCoord {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (Λ : AddSubgroup (WO S T))
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) : Prop :=
  (∀ x y, κ (x + y) = κ x + κ y) ∧ Set.BijOn κ {t | IsHalf a t} Set.univ ∧
    IsOpen (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∧ IsCompact (κ '' {t | t ∈ Λ ∧ IsHalf a t})

theorem wAt_eq_smul {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p w = idem D p • w := rfl

theorem onHalf_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) : onHalf φ S T BS BT e = pull e (mapCo φ S T BS BT) := rfl

theorem onHalfAdj_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) :
    onHalfAdj φ S T BS BT e = pull (cA D e) (adjCo φ S T BS BT) := rfl

theorem gAt_one (V : HSp D) (p : Place D) : gAt V p 1 = 1 := by
  cases p <;> simp [gAt]

theorem gAt_mul (V : HSp D) (p : Place D) (g g' : GA D V) : gAt V p (g * g') = gAt V p g * gAt V p g' := by
  cases p <;> simp [gAt]

theorem gAt_inv (V : HSp D) (p : Place D) (g : GA D V) : gAt V p g⁻¹ = (gAt V p g)⁻¹ := by
  cases p <;> simp [gAt]

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : FinPl D → Prop} (h : ∀ v, P v → Q v) : latO S T LS LT P ≤ latO S T LS LT Q := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hQ => hv v fun hP => hQ (h v hP), rest⟩

theorem isLatVac_mono {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ ≤ Λ') {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ' f) : IsLatVac hs Λ f := by
  unfold IsLatVac at hf ⊢
  exact ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f f₀ : WO S T → ℂ}

theorem vacAt_of_isLocal {p q : Place D} (h : IsLocal ψ θ S T sS sT ΛS ΛT p f) (hq : q ≠ p) :
    VacAt ψ θ S T sS sT ΛS ΛT q f := by
  rcases q with v | τ
  · exact isLatVac_mono (latO_mono fun u hu => hu ▸ hq) h.2.1
  · exact h.2.2 τ hq

theorem base_std (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsStdChar D ψ (-1) := by
  exact h.2.2.2.2.1

theorem base_inf (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsInfFam θ :=
  h.2.2.2.2.2.inf

theorem base_theta (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsThetaFunO ψ S T f₀ :=
  h.2.2.2.2.2.theta

theorem restrictedTensorBasePoint_norm_sq (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : nrm2 μ 𝓕 f₀ = 1 := by
  exact h.2.2.2.2.2.norm.2 (μ, 𝓕) hμ

theorem base_ne_zero (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : f₀ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨μ, 𝓕⟩, hq⟩ := h.2.2.2.2.2.norm.1
  have h1 := restrictedTensorBasePoint_norm_sq h hq
  simp [nrm2] at h1

theorem base_isLocal (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : IsLocal ψ θ S T sS sT ΛS ΛT p f₀ :=
  ⟨h.2.2.2.2.2.theta, isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat,
    fun τ _ => h.2.2.2.2.2.fock τ⟩

theorem base_vacAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : VacAt ψ θ S T sS sT ΛS ΛT p f₀ := by
  rcases p with v | τ
  · exact isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat
  · exact h.2.2.2.2.2.fock τ

end

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp

theorem tendsto_inf_mul_prod {L : Type} [Field L] [NumberField L] (χ : HChar L) (k : Lˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) Filter.atTop (nhds 1) := by
  have hlim := GlobalTheory.Mem.Chr.CharModel.tendsto_prod_local (F := L) k
  have hcont : Continuous fun a => ((χ.1 a : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  have h1 := (hcont.tendsto _).comp hlim
  have hd : ((χ.1 (GlobalTheory.Mem.Chr.diagUnits L k) : ℂˣ) : ℂ) = 1 := congrArg Units.val (χ.2.2 k)
  rw [hd] at h1
  refine h1.congr fun T => ?_
  simp only [Function.comp_apply, map_mul, map_prod, Units.val_mul, Units.coe_prod]
  rfl

theorem finite_bad {L : Type} [Field L] [NumberField L] (k : Lˣ) (N : ℕ) (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | ¬ (P.valuation L (k : L) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal)}.Finite := by
  have hS : (HeightOneSpectrum.Support (𝓞 L) (k : L) ∪ HeightOneSpectrum.Support (𝓞 L) ((k : L)⁻¹)).Finite :=
    (HeightOneSpectrum.Support.finite _ _).union (HeightOneSpectrum.Support.finite _ _)
  have hN0 : (N : 𝓞 L) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 L) L) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    omega
  have hD : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hN0)
  refine (hS.union hD).subset ?_
  intro P hP
  rw [Set.mem_ofPred_eq, not_and_or, not_not] at hP
  rcases hP with h | h
  · left
    rcases lt_or_gt_of_ne h with h' | h'
    · right
      show 1 < P.valuation L ((k : L)⁻¹)
      rw [map_inv₀]
      have h0 : P.valuation L (k : L) ≠ 0 := by simp
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h'⟩
    · left
      exact h'
  · right
    exact Ideal.dvd_span_singleton.mpr h

theorem eq_inf (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (k : D.host.Eˣ)
    (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y) (hy : infPart D (y : AE D) = 1)
    (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((c x : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hid := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hι2 hι3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hι2 hid c χ hc
  have hfin := finite_bad k N hN
  have hcomp : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      ι (finPart D (y : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) := by
    intro P
    rw [hy', hι1]
    exact GlobalTheory.CharLocProd.evalAt_algebraMap P (k : D.host.E)
  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (ι (finPart D (y : AE D)) P) = P.valuation D.host.E (k : D.host.E) := by
    intro P
    rw [hcomp]
    exact GlobalTheory.CharLocProd.val_algebraMap P _
  have hT : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.E)), hfin.toFinset ⊆ T →
      ((c y : Circle) : ℂ) = ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ) := by
    intro T hsub
    refine hprod y hy T (fun _ => k) (fun P _ => ⟨hval P, ?_⟩) (fun P hP => ?_)
    · rw [hcomp, sub_self, map_zero]
      exact zero_le
    · have hP' : P ∉ hfin.toFinset := fun h => hP (hsub h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hP'
      exact ⟨(hval P).trans hP'.1, hP'.2⟩
  have hev : (fun T : Finset (HeightOneSpectrum (𝓞 D.host.E)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) =ᶠ[Filter.atTop]
      fun _ => ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with T hsub
    rw [hT T hsub]
  have h1 : ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds ((tendsto_inf_mul_prod χ k).congr' hev)
  have h2 : ((c x : Circle) : ℂ) * ((c y : Circle) : ℂ) = 1 := by
    have h := hc.1.2 k
    rw [hxy, map_mul] at h
    rw [← Circle.coe_mul, h, Circle.coe_one]
  exact mul_right_cancel₀ (Circle.coe_ne_zero _) (h2.trans h1.symm)

private theorem coe_circle_exp_arg_eq_div_norm (z : ℂˣ) :
    ((Circle.exp (Complex.arg (z : ℂ)) : Circle) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := by
  rw [Circle.coe_exp]
  have hn : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (Units.ne_zero z))
  rw [eq_div_iff hn]
  linear_combination Complex.norm_mul_exp_arg_mul_I (z : ℂ)


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in
theorem hasInfExp_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ), ChrEq c χ → χ.HasInfQ (tauE D) a → ∀ τ, HasInfExp D c τ (a τ) := by
  intro D c χ a hc hχ τ
  obtain ⟨n, hn, hinf⟩ := hχ
  unfold HasInfExp AllSome
  refine ⟨n τ, hn τ, ?_, ?_⟩
  · obtain ⟨⟨θ0, hθ0⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun ρ => θ0 (tauE D ρ), fun ρ => hθ0 (tauE D ρ)⟩
  intro θ hθ x hx1 hx2
  obtain ⟨-, A, B, hA, -, hAB, hAparts, hBparts⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D

  let e : ℂˣ →* Circle := MonoidHom.mk' (fun z => Circle.exp (Complex.arg (z : ℂ))) (by
    intro z w
    apply Circle.ext
    rw [Circle.coe_mul, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, Units.val_mul, norm_mul,
      Complex.ofReal_mul, div_mul_div_comm])

  let h : D.what₂.Tau → ((AE D)ˣ →* Circle) := fun ρ =>
    (zpowGroupHom (n ρ)).comp (e.comp (Units.map ((θ ρ).comp (infPart D)).toMonoidHom))
  let g : (AE D)ˣ →* Circle := c.comp A * (∏ ρ, h ρ)⁻¹
  have hcoe : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), ((h ρ z : Circle) : ℂ) =
      (θ ρ (infPart D (z : AE D)) / ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ)) ^ (n ρ) := by
    intro z ρ
    show ((Circle.exp (Complex.arg ((Units.map ((θ ρ).comp (infPart D)).toMonoidHom z : ℂˣ) : ℂ)) ^ (n ρ) :
      Circle) : ℂ) = _
    rw [Circle.coe_zpow, coe_circle_exp_arg_eq_div_norm]
    rfl
  have hprodv : ∀ z : (AE D)ˣ, (((∏ ρ, h ρ) z : Circle) : ℂ) = ∏ ρ, ((h ρ z : Circle) : ℂ) := by
    intro z
    rw [MonoidHom.finsetProd_apply]
    exact map_prod Circle.coeHom (fun ρ => h ρ z) Finset.univ
  have hne : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), θ ρ (infPart D (z : AE D)) ≠ 0 := fun z ρ =>
    ((z.isUnit.map (infPart D)).map (θ ρ)).ne_zero
  have hcont_h : ∀ ρ, Continuous (h ρ) := by
    intro ρ
    apply continuous_induced_rng.mpr
    show Continuous fun z : (AE D)ˣ => ((h ρ z : Circle) : ℂ)
    simp_rw [hcoe]
    have hc1 : Continuous fun z : (AE D)ˣ => θ ρ (infPart D (z : AE D)) :=
      (continuous_comp hθ ρ).comp Units.continuous_val
    have hc2 : Continuous fun z : (AE D)ˣ => ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_norm.comp hc1)
    have hn2 : ∀ z : (AE D)ˣ, ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) ≠ 0 := fun z => by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne z ρ))
    exact (hc1.div hc2 hn2).zpow₀ (n ρ) fun z => Or.inl (div_ne_zero (hne z ρ) (hn2 z))
  have hP : Continuous fun z => (∏ ρ, h ρ) z := by
    simp_rw [MonoidHom.finsetProd_apply]
    exact continuous_finsetProd _ fun ρ _ => hcont_h ρ
  have hg_cont : Continuous g := by
    show Continuous fun z => c (A z) * ((∏ ρ, h ρ) z)⁻¹
    exact (hc.1.1.comp hA).mul hP.inv
  have hg_E : ∀ k : D.host.Eˣ, g (Units.map (incA D).toMonoidHom k) = 1 := by
    intro k
    have hAu : ((c (A (Units.map (incA D).toMonoidHom k)) : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
      refine eq_inf D c χ hc k _ (B (Units.map (incA D).toMonoidHom k)) (hAB _) (hBparts _).1 ?_
      rw [(hBparts _).2]
      show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    have hθk : ∀ ρ, θ ρ (infPart D ((Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
        tauE D ρ (k : D.host.E) := fun ρ => comp_incA hθ ρ (k : D.host.E)
    apply Circle.ext
    show ((c (A (Units.map (incA D).toMonoidHom k)) * ((∏ ρ, h ρ) (Units.map (incA D).toMonoidHom k))⁻¹ :
      Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, hprodv, hAu, Circle.coe_one]
    simp_rw [hcoe, hθk]
    rw [← hinf k]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have hg_fin : ∀ z : (AE D)ˣ, infPart D (z : AE D) = 1 → g z = 1 := by
    intro z hz
    have hA1 : A z = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
      (by rw [(hAparts z).1, hz, Units.val_one, map_one]) (by rw [(hAparts z).2, Units.val_one, map_one]))
    apply Circle.ext
    show ((c (A z) * ((∏ ρ, h ρ) z)⁻¹ : Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [hA1, map_one, one_mul, Circle.coe_inv, hprodv]
    simp_rw [hcoe, hz, map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one,
      inv_one, Circle.coe_one]
  have hg1 := eq_one_of_trivial_on_finite D g ⟨hg_cont, hg_E⟩ hg_fin
  have hB1 : B x = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [(hBparts x).1, Units.val_one, map_one]) (by rw [(hBparts x).2, hx1, Units.val_one, map_one]))
  have hxA : x = A x := by
    have hx := hAB x
    rw [hB1, mul_one] at hx
    exact hx
  have hcx : ((c x : Circle) : ℂ) = (((∏ ρ, h ρ) x : Circle) : ℂ) := by
    have hgx : c (A x) * ((∏ ρ, h ρ) x)⁻¹ = 1 := hg1 x
    rw [← hxA] at hgx
    rw [mul_inv_eq_one.mp hgx]
  rw [hcx, hprodv, Finset.prod_eq_single τ]
  · exact hcoe x τ
  · intro ρ _ hρ
    rw [hcoe, hx2 ρ hρ, norm_one, Complex.ofReal_one, div_one, one_zpow]
  · intro hτ
    exact absurd (Finset.mem_univ τ) hτ

end GlobalTheory.HeckeInfExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlacesLocalDatumBlockTriangularLaw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OmegaTwistLaw

section Fin
variable {κ : Type} [CommRing κ]

theorem lowZero_mul {a b c r : ℕ} {A : Matrix (Fin b) (Fin c) κ} {B : Matrix (Fin c) (Fin a) κ}
    (hA : LowZero r A) (hB : LowZero r B) : LowZero r (A * B) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases le_or_gt r l.val with hl | hl
  · rw [hB l j hl hj, mul_zero]
  · rw [hA i l hi hl, zero_mul]

theorem topL_eq {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (A : Matrix (Fin b) (Fin a) κ) :
    topL r A = A.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  show (if h : i.val < b ∧ j.val < a then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0) = A (Fin.castLE hb i) (Fin.castLE ha j)
  rw [dite_eq_left hij]
  rfl

theorem topL_mul {a b c r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (A : Matrix (Fin b) (Fin c) κ)
    {B : Matrix (Fin c) (Fin a) κ} (hB : LowZero r B) : topL r (A * B) = topL r A * topL r B := by
  rw [topL_eq ha hb, topL_eq hc hb, topL_eq ha hc]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hc) (Fin.castLE_injective hc) _ _ (fun l hl => ?_) (fun l => rfl)
  have hlr : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, Fin.ext rfl⟩
  rw [hB l _ hlr (by simp), mul_zero]

theorem lowZero_of_mem {n r : ℕ} {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) : LowZero r g.val := by
  intro i j hi hj
  refine mem_blockTri.mp h i j ?_
  have h1 : blk2 r i = 1 := if_neg (not_lt.mpr hi)
  have h0 : blk2 r j = 0 := if_pos hj
  rw [h0, h1]
  exact Nat.zero_lt_one

theorem det_eq {n r : ℕ} (hr : r ≤ n) {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  have hg : (g.val).BlockTriangular (blk2 r) := fun i j hij => mem_blockTri.mp h i j hij
  let e : Fin r ≃ {x : Fin n // blk2 r x = 0} :=
    { toFun := fun i => ⟨Fin.castLE hr i, if_pos (by simp)⟩
      invFun := fun x => ⟨x.1.val, by
        have hx := x.2
        unfold blk2 at hx
        split_ifs at hx with hlt
        exact hlt⟩
      left_inv := fun i => Fin.ext rfl
      right_inv := fun x => Subtype.ext (Fin.ext rfl) }
  have hsub : (g.val.toSquareBlock (blk2 r) 0).submatrix e e = g.val.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext i j
    rfl
  ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, diag_block_det_val 1 h, hg.det, ← hsub, Matrix.det_submatrix_equiv_self]
  have hsub2 : Finset.univ.image (blk2 (n := n) r) ⊆ {0, 1} := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    unfold blk2
    split_ifs <;> simp
  rw [Finset.prod_subset hsub2 (fun x _ hx => ?_), Finset.prod_pair zero_ne_one]
  · rfl
  · haveI : IsEmpty {y : Fin n // blk2 r y = x} :=
      ⟨fun y => hx (Finset.mem_image.mpr ⟨y.1, Finset.mem_univ _, y.2⟩)⟩
    exact Matrix.det_isEmpty

theorem det_topL {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((gT⁻¹).val * y * gS.val)).det =
      ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb gT))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha gS) : κˣ) *
        (topL r y).det := by
  have hTi : gT⁻¹ ∈ blockTri (blk2 r) := inv_mem hT
  have hinv : upperLeftBlock hb gT⁻¹ = (upperLeftBlock hb gT)⁻¹ := extendOne_inv (blkR hb) hT
  rw [topL_mul ha hb ha ((gT⁻¹).val * y) (lowZero_of_mem hS), topL_mul ha hb hb (gT⁻¹).val hy,
    Matrix.det_mul, Matrix.det_mul, topL_eq ha ha gS.val, topL_eq hb hb (gT⁻¹).val, ← upper_block_val_submatrix ha hS,
    ← upper_block_val_submatrix hb hTi, hinv, ← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv, Units.val_mul]
  ring

theorem lowZero_iff {a b r : ℕ} {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) (y : Matrix (Fin b) (Fin a) κ) :
    LowZero r ((gT⁻¹).val * y * gS.val) ↔ LowZero r y := by
  have hS' := lowZero_of_mem hS
  have hTi := lowZero_of_mem (inv_mem hT)
  constructor
  · intro h
    have hy : y = gT.val * ((gT⁻¹).val * y * gS.val) * (gS⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_mem hT) h) (lowZero_of_mem (inv_mem hS))
  · intro h
    exact lowZero_mul (lowZero_mul hTi h) hS'

end Fin

theorem omegaQ_blockTri : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  intro D a b r ha hb Q ξ k gS gT y y' hS hT hy'
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) → (topL r (y' PP)).det =
      (((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT PP)))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS PP)) :
        (kP PP)ˣ) : kP PP) * (topL r (y PP)).det := fun PP hPP hl => by
    rw [hy' PP hPP]
    exact det_topL ha hb (hS PP hPP) (hT PP hPP) hl
  have hcond : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hPP => ?_
    have hlz : LowZero r (y' PP) ↔ LowZero r (y PP) := by
      rw [hy' PP hPP]
      exact lowZero_iff (hS PP hPP) (hT PP hPP) (y PP)
    rw [hlz]
    refine and_congr_right fun hl => ?_
    rw [hdet PP hPP hl, Units.isUnit_units_mul]
  have hsplit : ∀ (A : Pl D.host.E → ℂ) (U : Q → ℂ),
      (∏ PP ∈ Q, A PP) ^ k * ∏ PP ∈ Q.attach, U PP ^ k = ∏ PP ∈ Q.attach, (A PP.1 * U PP) ^ k := by
    intro A U
    rw [← Finset.prod_attach Q A, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    simp only [mul_zpow]
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · have h' := hcond.mpr h
    rw [dite_eq_left h', dite_eq_left h, hsplit, hsplit]
    refine Finset.prod_congr rfl fun PP _ => ?_
    congr 1
    obtain ⟨P, hP⟩ := PP
    have eS := det_eq ha (hS P hP)
    have eT := det_eq hb (hT P hP)
    have eU : (h' P hP).2.unit = ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT P)))⁻¹ *
        Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS P))) * (h P hP).2.unit := by
      ext
      rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec]
      exact hdet P hP (h P hP).1
    simp only []
    rw [eS, eT, eU]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have h' : ¬ ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det := fun h'' => h (hcond.mp h'')
    rw [dite_eq_right h', dite_eq_right h, mul_zero, mul_zero]

end GlobalTheory.OmegaTwistLaw

end
end

