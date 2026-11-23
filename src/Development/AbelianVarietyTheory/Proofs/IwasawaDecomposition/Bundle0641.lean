module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistOfOneField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem GlobalTheory.CommonReading.norm_aut {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem GlobalTheory.CommonReading.norm_aut_le {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (x : Formalism.L2.TwC.intOf l K) : ‖τ x‖ ≤ 1 := by
  rw [GlobalTheory.CommonReading.norm_aut, ← PadicAlgCl.valuation_coe]
  exact_mod_cast x.2.2

namespace GlobalTheory.HeightCounting.SameTw

def Reads (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) {Λ : Type} [Field Λ] (e : D.what₂.LL →+* Λ)
    (φ : D.ntw.O0 (C.twI w) →+* Λ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (τ : Λ →+* Ω) (ι : FractionRing (C.Oe w) →+* Ω),
    (∀ y, τ (φ y) = ι (algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) y)))) ∧
    ∀ x : D.what₂.LL, τ (e x) = ι (C.embW w x)

theorem exists_reads (D : D7) (C : NChoice D) (F : TwFrameC D) {low : Finset ℕ} (hF : TwistFrameLowIndexCompatibility D F low) (w : D.what₂.places.Pl)
    (l : ℕ) [Fact l.Prime] (hl : D.ntw.l (C.twI w) = l) (e : D.what₂.LL →+* PadicAlgCl l)
    (he : ∀ x, 0 ≤ D.what₂.places.val w x ↔ ‖e x‖ ≤ 1) :
    ∃ φ : D.ntw.O0 (C.twI w) →+* PadicAlgCl l, Reads D C w e φ ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
      (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ y, φ y ∈ K) ∧
      ∀ (z : ℤ_[D.ntw.l (C.twI w)]) (z' : ℤ_[l]), HEq z z' →
        φ (algebraMap _ (D.ntw.O0 (C.twI w)) z) = algebraMap ℚ_[l] (PadicAlgCl l) (z' : ℚ_[l]) := by
  subst hl
  haveI := C.Oe_fin w
  obtain ⟨σ, ι, h1, h2⟩ := GlobalTheory.CommonReading.exists_common (C.Oe_inj w)
    ((Subring.subtype _).comp (F.eOk (C.twI w) (C.k' w)).toRingHom)
    (Subtype.val_injective.comp (F.eOk (C.twI w) (C.k' w)).injective)
    (fun y => (F.eOk (C.twI w) (C.k' w) y).2.2) (C.embW w) e fun x => (C.embW_w w x).symm.trans (he x)
  refine ⟨σ.symm.toAlgHom.toRingHom.comp ((Subring.subtype _).comp (F.eO0 (C.twI w)).toRingHom),
    ⟨ℂ_[D.ntw.l (C.twI w)], inferInstance, (algebraMap (PadicAlgCl (D.ntw.l (C.twI w))) ℂ_[D.ntw.l (C.twI w)]).comp
      σ.toAlgHom.toRingHom, ι, fun y => ?_,
      fun x => (h2 x).symm⟩, fun y => ?_, ⟨(F.K0 (C.twI w)).1.map σ.symm.toAlgHom, ?_, fun y => ⟨_, (F.eO0 (C.twI w) y).2.1, rfl⟩⟩, ?_⟩
  · rw [h1]
    refine Eq.trans ?_ ((hF.eOk_alg _ _ _).trans (hF.eO_alg _ y)).symm
    simp
  · exact GlobalTheory.CommonReading.norm_aut_le σ.symm _ (F.eO0 (C.twI w) y)
  · haveI := (F.K0 (C.twI w)).2
    exact LinearEquiv.finiteDimensional (IntermediateField.equivMap _ σ.symm.toAlgHom).toLinearEquiv
  · rintro z _ ⟨⟩
    change σ.symm (F.eO0 (C.twI w) _ : PadicAlgCl _) = _
    rw [hF.ringSpec_baseIntegersEquiv_algebraMap, AlgEquiv.commutes]

theorem Reads.emb {D : D7} {C : NChoice D} (hC : ChoiceC D C) {w : D.what₂.places.Pl} (hw : TwistedAt D w) {Λ : Type} [Field Λ]
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w e φ) (x : D.LL0) (y : D.ntw.O0 (C.twI w))
    (hy : algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y =
      (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x) : e x = φ y := by
  obtain ⟨Ω, _, τ, ι, h1, h2⟩ := h
  apply τ.injective
  rw [h1, h2, hC.emb_side w hw x]
  have : (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x) =
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y := by
    rw [hy]; split_ifs <;> rfl
  rw [this, fracOe, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem Reads.of_comp {D : D7} {C : NChoice D} {w : D.what₂.places.Pl} {Λ Λ' : Type} [Field Λ] [Field Λ'] (q : Λ →+* Λ')
    {e : D.what₂.LL →+* Λ} {φ : D.ntw.O0 (C.twI w) →+* Λ} (h : Reads D C w (q.comp e) (q.comp φ)) : Reads D C w e φ :=
  let ⟨Ω, i, τ, ι, h1, h2⟩ := h
  ⟨Ω, i, τ.comp q, ι, h1, h2⟩

def OneField (D : D7) (C : NChoice D) : Prop :=
  ∀ a : D.nd.Loc, ∃ f : D.ntw.O0 (C.twI (D.nd.w a)) →+* D.nd.O a, HEq f (D.ntw.twist₂ a) ∧
    Reads D C (D.nd.w a) (D.nd.embK a) ((algebraMap (D.nd.O a) (FractionRing (D.nd.O a))).comp f)

def TwReads {D : D7} (C : NChoice D) (X : LocNd (lay0 D)) (T : LocTw X) : Prop :=
  ∀ a : X.nd.Loc, ∃ f : D.ntw.O0 (C.twI (X.nd.w a)) →+* X.nd.O a, HEq f (T.twist₂ a) ∧
    Reads D C (X.nd.w a) (X.nd.embK a) ((algebraMap (X.nd.O a) (FractionRing (X.nd.O a))).comp f)


set_option maxHeartbeats 2000000 in
theorem oneField_withLoc {D : D7} (L : LocAll (lay0 D)) (C : NChoice D) :
    OneField (withLoc L) (chL L C) ↔ TwReads C L.X L.T := Iff.rfl

theorem sameChar_of_inj {O₀ O₁ O₂ Γ Ω : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ] [CommRing Ω]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) (j₁ : O₁ →+* Ω) (j₂ : O₂ →+* Ω)
    (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂) (hf : ∀ y, j₁ (f₁ y) = j₂ (f₂ y))
    (hψ : ∀ g, j₁ (ψ₁ g : O₁ˣ) = j₂ (ψ₂ g : O₂ˣ)) : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂ := by
  intro F
  rw [← map_eq_zero_iff j₁ h₁, ← map_eq_zero_iff j₂ h₂]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_mul, hf, hψ]

theorem sameTwist_of_oneField (D : D7) (C : NChoice D) (hT : NChTie D C) (h : OneField D C) : GlobalTheory.PtCore.SameTwist D C := by
  intro a
  obtain ⟨f, hf, Ω, _, ιA, ιB, h1, h2⟩ := h a
  obtain ⟨ψ0, -, hw, hl⟩ := hT.psi_eq
  refine (GlobalTheory.PtCore.sameTwistAt_iff D a _ _ _).2 ⟨hT.twOf_eq a, f, hf, ?_⟩
  refine sameChar_of_inj _ _ _ _ (ιA.comp (algebraMap (D.nd.O a) (FractionRing (D.nd.O a))))
    (ιB.comp ((algebraMap (C.Oe (D.nd.w a)) (FractionRing (C.Oe (D.nd.w a)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w a)) (C.k' (D.nd.w a))) (C.Oe (D.nd.w a)))))
    (ιA.injective.comp (IsFractionRing.injective _ _))
    (ιB.injective.comp ((IsFractionRing.injective (C.Oe (D.nd.w a)) _).comp (C.Oe_inj _))) h1 fun g => ?_
  have := h2 ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL)
  rw [hl, hw] at this
  exact this

end GlobalTheory.HeightCounting.SameTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan.StarOnCell

variable {X : Type} [AddCommGroup X]

theorem ell_of_eq {n : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    {u : Fin n → LinearMap.BilinForm ℤ X} {c : Fin n → ℝ} (h : toReal β = ∑ i, c i • toReal (u i)) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) c : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, h]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem ell_of_sub_mem {m : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β v : LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {t : ℝ} (h : toReal β - t • toReal v ∈ rcone γ) :
    ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ (ℓ β : ℝ) = t * ℓ v + ∑ j, d j * ℓ (γ j) := by
  obtain ⟨d, hd, e⟩ := h
  refine ⟨d, hd, ?_⟩
  have e' : toReal β = ∑ i : Fin (m + 1), (Fin.cons t d : Fin (m + 1) → ℝ) i •
      toReal ((Fin.cons v γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← e]
    abel
  rw [ell_of_eq ℓ e', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem inRCone_of_sum {p n : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {u : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i) (e : toReal β = ∑ i, x i • toReal (δ i))
    (h : ∀ i, x i ≠ 0 → InRCone u (δ i)) : InRCone u β := by
  classical
  have hi : ∀ i, ∃ g : Fin n → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (u j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨c, hc, hcs⟩ := h i h0
    exact ⟨fun j => x i * c j, fun j => mul_nonneg (hx i) (hc j), by
      rw [hcs, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [e, Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem exists_nat_of_inRCone {n : ℕ} (u : Fin n → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : InRCone u β) : ∃ (k : ℕ) (c : Fin n → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  obtain ⟨r, v, hiff, -⟩ := GlobalTheory.MinkWeylReal.cone_orthant_fg (n + 1) ∅
    (Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ))
    Set.finite_empty
  have h1 : (∀ i, 0 ≤ (Fin.cons 1 c : Fin (n + 1) → ℝ) i) ∧
      (∀ a ∈ (∅ : Set (Fin (n + 1) → ℤ)), ∑ i, (a i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i ≤ 0) ∧
      (∀ b ∈ Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ),
        ∑ i, (b i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i = 0) := by
    refine ⟨fun i => Fin.cases (by simp) (fun j => by simpa using hc j) i, by simp, ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have he := LinearMap.congr_fun₂ e a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg, mul_one]
    rw [he]
    rw [show ∑ i, (u i a b : ℝ) * c i = ∑ i, c i * (u i a b : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨e', he', ht⟩ := (hiff _).1 h1
  have h0 := congr_fun ht 0
  simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  obtain ⟨k, hk⟩ : ∃ k, v k 0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    simp [hne] at h0
  have hv := (hiff fun i => (v k i : ℝ)).2 ⟨Pi.single k 1, fun j => by
    by_cases h : j = k <;> simp [Pi.single_apply, h], by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp⟩
  obtain ⟨-, -, hV⟩ := hv
  refine ⟨v k 0, fun i => v k i.succ, Nat.pos_of_ne_zero hk, ?_⟩
  ext a b
  have h2 := hV _ ⟨(a, b), rfl⟩
  rw [Fin.sum_univ_succ] at h2
  simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg] at h2
  have h3 : ((v k 0 : ℤ) * β a b : ℝ) = ((∑ i, (v k i.succ : ℤ) * u i a b : ℤ) : ℝ) := by
    push_cast
    rw [show ∑ i, ((v k i.succ : ℝ) * (u i a b : ℝ)) = ∑ i, (u i a b : ℝ) * (v k i.succ : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    linarith
  have h4 : (v k 0 : ℤ) * β a b = ∑ i, (v k i.succ : ℤ) * u i a b := by exact_mod_cast h3
  simpa [LinearMap.sum_apply] using h4

end GlobalTheory.PolFan.StarOnCell

namespace GlobalTheory.PolFan.StarOnCell

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem mul_starDepth_le (hγ : IsCell bar ψ γ) {β₀ : LinearMap.BilinForm ℤ X}
    (huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hh : ∀ j, 0 ≤ h (γ j)) (hpos : 0 < h β₀)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hhβ : (0 : ℝ) ≤ h β := by
    rw [ell_of_eq h e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hh i)
  have key := evalR_starDepth_le O bar ψ w X m γ (toReal β) ((h β : ℝ) / h β₀) hγ ⟨c, hc, e⟩
    (div_nonneg hhβ hpos'.le) (fun v hv hvp hwv hvin t ht hrest => by
      obtain rfl := huniq v hv hvp hwv hvin
      obtain ⟨d, hd, hrel⟩ := ell_of_sub_mem h hrest
      rw [le_div_iff₀ hpos']
      have : (0 : ℝ) ≤ ∑ j, d j * h (γ j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (by exact_mod_cast hh j)
      linarith)
  rw [evalR_toReal] at key
  calc (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β₀ * ((h β : ℝ) / h β₀) :=
        mul_le_mul_of_nonneg_left key hpos'.le
    _ = h β := by field_simp

end GlobalTheory.PolFan.StarOnCell


open GlobalTheory.PolFan.StarOnCell in
theorem GlobalTheory.PolFan.starDepth_on_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X,
    (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧
    (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β →
      ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧
        k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro E _ _ _ H q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := _root_.GlobalTheory.PolFan.depth_le_starDepth (𝓞 E) H.bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth H.bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
    nlinarith
  ·
    intro β _ _ hβ heq
    have hβr : toReal β ∈ rcone γ := by obtain ⟨c, hc0, e⟩ := hβ; exact ⟨c, hc0, e⟩
    obtain ⟨m'', s'', h'', hf'', hpos'', t, ht, e⟩ :=
      GlobalTheory.StarCover.star_cover X m γ β₀ (toReal β) (fun i => (hγ.mem i).1) hγ.nonneg hne hin hβr
    have hpos''' : (0 : ℝ) < h'' β₀ := by exact_mod_cast hpos''

    have r2 := ell_of_eq h'' e
    rw [Fin.sum_univ_succ] at r2
    simp only [Fin.cons_zero, Fin.cons_succ] at r2
    have z2 : ∀ j, (h'' (γ (s'' j)) : ℝ) = 0 := fun j => by
      rw [(hf''.2 (s'' j)).2 ⟨j, rfl⟩, Int.cast_zero]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero] at r2
    have hle : (starDepth H.bar ψ w).evalZ β ≤ t 0 := by
      have := mul_starDepth_le hγ huniq h'' hf''.1 hpos'' hβ
      rw [r2] at this
      nlinarith

    have r1 := ell_of_eq h e
    rw [Fin.sum_univ_succ] at r1
    simp only [Fin.cons_zero, Fin.cons_succ] at r1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ t j.succ * (h (γ (s'' j)) : ℝ) := fun j _ =>
      mul_nonneg (ht _) (by exact_mod_cast hf.1 _)
    have hsum : ∑ j, t j.succ * (h (γ (s'' j)) : ℝ) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have hcone : InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) β := by
      refine inRCone_of_sum t ht e fun i hi => ?_
      refine Fin.cases (fun _ => ?_) (fun j hj => ?_) i hi
      · simpa using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) 0
      · have h0 : (h (γ (s'' j)) : ℝ) = 0 := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_left hj
        have h0' : h (γ (s'' j)) = 0 := by exact_mod_cast h0
        obtain ⟨k, hk⟩ := (hf.2 (s'' j)).1 h0'
        simpa [hk] using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k.succ
    exact exists_nat_of_inRCone _ β hcone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem sum_extend_smul_starLin {M : Type} [AddCommMonoid M] [Module ℝ M] {m m' : ℕ} (s : Fin m' ↪ Fin m)
    (d : Fin m' → ℝ) (f : Fin m → M) : ∑ i, Function.extend s d 0 i • f i = ∑ j, d j • f (s j) := by
  symm
  refine Fintype.sum_of_injective s s.injective _ _ (fun i hi => ?_) fun j => by rw [s.injective.extend_apply]
  rw [Function.extend_apply' _ _ _ hi]; simp

theorem extend_nonneg_starLin {m m' : ℕ} (s : Fin m' ↪ Fin m) {d : Fin m' → ℝ} (hd : ∀ j, 0 ≤ d j) (i : Fin m) :
    0 ≤ Function.extend s d 0 i := by
  by_cases hi : ∃ j, s j = i
  · obtain ⟨j, rfl⟩ := hi; rw [s.injective.extend_apply]; exact hd j
  · rw [Function.extend_apply' _ _ _ hi]; rfl

theorem starFun_linearOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w K D hcent
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX m γ hγ hno
    have ps0 : ∀ B ∈ rcone γ, evalR (starDepth H.bar ψ w) B = 0 := fun B hB =>
      le_antisymm (_root_.GlobalTheory.PolFan.evalR_starDepth_le _ H.bar ψ w X m γ B 0 hγ hB le_rfl fun v hv hp hw hin _ _ _ =>
        absurd (hno v hv hp hin) (by rw [hw]; norm_num)) (starDepth_eval_nonneg _)
    have psγ : ∀ i, (starDepth H.bar ψ w).evalZ (γ i) = 0 := fun i => by
      rw [← evalR_toReal]; exact ps0 _ (inRCone_self γ i)
    rw [linearOn_iff]
    intro c hc
    rw [starFun_evalR, (linearOn_iff ψ γ).1 hγ.linear c hc, ps0 _ ⟨c, hc, rfl⟩, add_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [starFun_evalZ, psγ i]; ring
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hh
    obtain ⟨-, hC2, hC3⟩ := hcent X hX
    have uniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
      fun v hv hp hw hin => hC3 m γ hγ v hv hp β₀ hβ₀ hp₀ hw hw₀ hin hin₀
    have hne : β₀ ≠ 0 := by
      rintro rfl
      have := hC2 0 hβ₀ hp₀ hw₀ 2 0 (by simp)
      norm_num at this
    obtain ⟨e, he, hβe⟩ := id hin₀
    have coords : ∀ (a : ℝ) (d : Fin m' → ℝ), a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) =
        ∑ i, (a * e i + Function.extend s d 0 i) • toReal (γ i) := fun a d => by
      rw [hβe, Finset.smul_sum, ← sum_extend_smul_starLin s d (fun i => toReal (γ i))]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib]
    have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hcut.2 (s j)).2 ⟨j, rfl⟩
    have psv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR (starDepth H.bar ψ w) (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a := by
      intro a d ha hd
      have hB : a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) ∈ rcone γ :=
        ⟨fun i => a * e i + Function.extend s d 0 i,
          fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i), coords a d⟩
      refine le_antisymm (_root_.GlobalTheory.PolFan.evalR_starDepth_le _ H.bar ψ w X m γ _ a hγ hB ha fun v hv hp hw hin t ht hBt => ?_)
        (_root_.GlobalTheory.PolFan.depth_le_starDepth _ H.bar ψ w X m γ _ β₀ a hγ hB hβ₀ hp₀ hw₀ hin₀ hne uniq ha ?_)
      · rw [uniq v hv hp hw hin] at hBt
        obtain ⟨g, hg, hBg⟩ := hBt
        have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) h
          (β := Sum.elim (fun j => γ (s j)) (fun o : Option (Fin m) => o.elim β₀ γ))
          (c := Sum.elim d (fun o : Option (Fin m) => o.elim (a - t) fun i => -g i)) (by
            simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
              LinearMap.id_apply, neg_smul, Finset.sum_neg_distrib]
            rw [← hBg, sub_smul]
            abel)
        simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
          hs0, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, neg_mul, Finset.sum_neg_distrib] at rel
        have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hcut.1 i)
        have hh' : (0 : ℝ) < h β₀ := by exact_mod_cast hh
        nlinarith
      · exact ⟨Function.extend s d 0, extend_nonneg_starLin s hd, by
          rw [add_sub_cancel_left, sum_extend_smul_starLin]⟩
    have psβ : (starDepth H.bar ψ w).evalZ β₀ = 1 := by
      have := psv 1 0 zero_le_one fun _ => le_rfl
      simpa using this
    have psγs : ∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0 := fun j => by
      have := psv 0 (Pi.single j 1) le_rfl fun i => by by_cases hi : i = j <;> simp [Pi.single_apply, hi]
      simpa [Pi.single_apply] using this
    have ψv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR ψ (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a * ψ.evalZ β₀ + ∑ j, d j * ψ.evalZ (γ (s j)) := by
      intro a d ha hd
      have hψβ : ψ.evalZ β₀ = ∑ i, e i * ψ.evalZ (γ i) := by
        rw [← evalR_toReal, hβe, (linearOn_iff ψ γ).1 hγ.linear e he]
      have hx := sum_extend_smul_starLin s d fun i => ψ.evalZ (γ i)
      simp only [smul_eq_mul] at hx
      rw [coords, (linearOn_iff ψ γ).1 hγ.linear _
        (fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i)), hψβ, Finset.mul_sum, ← hx]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib]
    rw [linearOn_iff]
    intro c hc
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [starFun_evalR, ψv _ _ (hc 0) (fun j => hc _), psv _ _ (hc 0) (fun j => hc _), starFun_evalZ, psβ]
    simp only [starFun_evalZ, psγs, add_zero]
    have e1 : ∑ j : Fin m', c j.succ * ((D : ℝ) * (K * ψ.evalZ (γ (s j)))) =
        D * K * ∑ j : Fin m', c j.succ * ψ.evalZ (γ (s j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; ring

end GlobalTheory.PolFan
end
end

