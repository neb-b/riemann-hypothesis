module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedEigenLatticeLeSpanIntegralFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotMatch

def complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) : {s : Fin a' → Fin d // StrictMono s} :=
  ⟨Finset.orderEmbOfFin (Finset.univ.image s.1)ᶜ (by
      rw [Finset.card_compl, Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fin]; omega), (Finset.orderEmbOfFin _ _).strictMono⟩

theorem range_complSub {a a' d : ℕ} (h : a + a' = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    Set.range (complSub h s).1 = (Set.range s.1)ᶜ := by
  simp only [complSub, Finset.range_orderEmbOfFin, Finset.coe_compl, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem complSub_complSub {a a' d : ℕ} (h : a + a' = d) (h' : a' + a = d) (s : {s : Fin a → Fin d // StrictMono s}) :
    complSub h' (complSub h s) = s := by
  apply Subtype.ext
  apply (StrictMono.range_inj (complSub h' (complSub h s)).2 s.2).1
  rw [range_complSub, range_complSub, compl_compl]

def complTup (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) (T : Tup D a d n) : Tup D a' d n :=
  fun τ k => complSub h (T τ k)

theorem complTup_bijective (D : D7) {a a' d : ℕ} {n : D.what₂.Tau → ℕ} (h : a + a' = d) :
    Function.Bijective (complTup D (n := n) h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨complTup D (a := a') (a' := a) (by omega), fun T => ?_, fun T => ?_⟩ <;>
    funext τ k <;> simp only [complTup, complSub_complSub]

theorem exists_signed_perm {α β : Type} [Fintype α] [Fintype β] (c : α → β) (hc : Function.Bijective c) (ε : α → ℤˣ) :
    ∃ (M : α → β → ℤ) (M' : β → α → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
      ∀ T (f : β → ℂ), ∑ T', (M T T' : ℂ) * f T' = ((ε T : ℤ) : ℂ) * f (c T) := by
  classical
  refine ⟨fun T T' => if T' = c T then (ε T : ℤ) else 0, fun T' T => if T' = c T then (ε T : ℤ) else 0, fun T₁ T₂ => ?_,
    fun T f => ?_⟩
  · obtain ⟨T, rfl⟩ := hc.2 T₁
    rw [Finset.sum_eq_single T]
    · by_cases h : c T = T₂
      · subst h; simp [← Units.val_mul]
      · simp [h, Ne.symm h]
    · intro b _ hb
      have : c T ≠ c b := fun e => hb (hc.1 e).symm
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (c T)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end GlobalTheory.BotMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedEigenLatticeLeSpanIntegralFrameStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_eigenLattice_le_span_integral_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  first | exact @GlobalTheory.EigLatSpan.eigLat_le_span | exact GlobalTheory.EigLatSpan.eigLat_le_span | (intros; apply GlobalTheory.EigLatSpan.eigLat_le_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchrodingerCompatibility
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.GenRep

theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (φ₁ φ₂ : (κ → R) → ℂ) :
    d.rho ψ w (φ₁ + φ₂) = d.rho ψ w φ₁ + d.rho ψ w φ₂ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (c : ℂ) (φ : (κ → R) → ℂ) :
    d.rho ψ w (c • φ) = c • d.rho ψ w φ := by
  funext x; simp [Darboux.rho, schr]; ring

theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) :
    d.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]


open scoped Classical in
theorem genRep : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsBy τ C ω₀ Φ (fockAct2 P Q R S) c₀ := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := GlobalTheory.T.theta_lift_darboux_adelic_symplectic hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := _root_.GlobalTheory.SliceExt.exists_rep_pure F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add (f := _), map_add (f := _), hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    convert hder γ hγ Y hY T L using 1
    · funext t
      exact (congrArg l (hω (γ (Multiplicative.ofAdd t)) (Φ T) h)).trans (hL _)
    · exact hL _

end GlobalTheory.GenRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Decomposition
section
open Matrix

namespace GlobalTheory.UnipotentCongruenceInverse

section Ring
variable {R M : Type} [CommRing R] [Ring M] [Algebra R M]

theorem cong_mul {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hy : (1 - e) • (y - 1) = 0) :
    (1 - e) • (x * y - 1) = 0 := by
  have h1 : x * y - 1 = (x - 1) * y + (y - 1) := by noncomm_ring
  rw [h1, smul_add, ← smul_mul_assoc, hx, zero_mul, zero_add, hy]

theorem cong_inv {e : R} {x y : M} (hx : (1 - e) • (x - 1) = 0) (hxy : y * x = 1) :
    (1 - e) • (y - 1) = 0 := by
  have h1 : y - 1 = -(y * (x - 1)) := by rw [mul_sub, hxy, mul_one]; abel
  rw [h1, smul_neg, ← mul_smul_comm, hx, mul_zero, neg_zero]

theorem key {e : R} {k K h h' a b : M} (hKk : K * k = 1) (hh : h' * h = 1)
    (hK : (1 - e) • (K - 1) = 0) (hhe : (1 - e) • (h - 1) = 0)
    (ha : (1 - k) * a = e • (1 : M)) (hb : b * (1 - h') = e • (1 : M)) :
    (K - 1) * (1 - (b - a) * (h - 1)) = h - 1 := by

  have hu : e • (K - 1) = K - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hK; exact hK.symm
  have hv : e • (h - 1) = h - 1 := by
    rw [sub_smul, one_smul, sub_eq_zero] at hhe; exact hhe.symm
  have hua : (K - 1) * a = e • K := by
    have hK1 : K - 1 = K * (1 - k) := by rw [mul_sub, mul_one, hKk]
    rw [hK1, mul_assoc, ha, mul_smul_comm, mul_one]
  have hbv : b * (h - 1) = e • h := by
    have hh1 : h - 1 = (1 - h') * h := by rw [sub_mul, one_mul, hh]
    rw [hh1, ← mul_assoc, hb, smul_mul_assoc, one_mul]
  calc (K - 1) * (1 - (b - a) * (h - 1))
      = (K - 1) - (K - 1) * (b * (h - 1)) + ((K - 1) * a) * (h - 1) := by noncomm_ring
    _ = (K - 1) - (e • (K - 1)) * h + K * (e • (h - 1)) := by
        rw [hbv, hua]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = h - 1 := by rw [hu, hv]; noncomm_ring

end Ring

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {β : Type} [Fintype β] [DecidableEq β]

theorem cayley (c : A →ₐ[R] A) {J k a : Matrix β β A} {e : R} (hk : kᵀ * J * k.map c = J) (hea : e • a = a)
    (ha : (1 - k) * a = e • (1 : Matrix β β A)) (he : e * e = e) : aᵀ * J + J * a.map c = e • J := by
  have hT : aᵀ * (1 - k)ᵀ = e • (1 : Matrix β β A) := by
    rw [← transpose_mul, ha, transpose_smul, transpose_one]
  have hac : (1 - k.map c) * a.map c = e • (1 : Matrix β β A) := by
    have h1 := congrArg c.mapMatrix ha
    rwa [map_mul, map_sub, map_one, map_smul, map_one, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply] at h1
  have heac : e • a.map c = a.map c := by
    have h1 := congrArg c.mapMatrix hea
    rwa [map_smul, AlgHom.mapMatrix_apply] at h1
  have heaT : e • aᵀ = aᵀ := by rw [← transpose_smul, hea]

  have hid : (1 - k)ᵀ * J * (1 - k.map c) = (1 - k)ᵀ * J + J * (1 - k.map c) := by
    rw [transpose_sub, transpose_one]
    have e1 : (1 - kᵀ) * J * (1 - k.map c)
        = (1 - kᵀ) * J + J * (1 - k.map c) + (kᵀ * J * k.map c - J) := by noncomm_ring
    rw [e1, hk, sub_self, add_zero]
  have main : aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c = e • J := by
    calc aᵀ * ((1 - k)ᵀ * J * (1 - k.map c)) * a.map c
        = (aᵀ * (1 - k)ᵀ) * J * ((1 - k.map c) * a.map c) := by simp only [Matrix.mul_assoc]
      _ = e • J := by
          rw [hT, hac, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul, he]
  have t1 : aᵀ * ((1 - k)ᵀ * J) * a.map c = J * a.map c := by
    rw [← Matrix.mul_assoc, hT, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      ← Matrix.mul_smul, heac]
  have t2 : aᵀ * (J * (1 - k.map c)) * a.map c = aᵀ * J := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hac, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_smul, ← Matrix.smul_mul, heaT]
  rw [hid, Matrix.mul_add, Matrix.add_mul, t1, t2] at main
  rw [add_comm]
  exact main

def unip (N : Matrix β β A) : GL (β ⊕ β) A where
  val := fromBlocks (1 + N) (-N) N (1 - N)
  inv := fromBlocks (1 - N) N (-N) (1 + N)
  val_inv := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring
  inv_val := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> noncomm_ring

theorem unip_mem (c : A →ₐ[R] A) {J N : Matrix β β A} (hN : Nᵀ * J + J * N.map c = 0) :
    unip N ∈ GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) := by
  show ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * GlobalTheory.WeilM.dbl J *
      ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A).map c = GlobalTheory.WeilM.dbl J
  have hU : ((unip N : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) =
      fromBlocks (1 + N) (-N) N (1 - N) := rfl
  have hm1 : (1 + N).map c = 1 + N.map c := by
    have h := map_add c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  have hm2 : (-N).map c = -N.map c := map_neg c.mapMatrix N
  have hm3 : (1 - N).map c = 1 - N.map c := by
    have h := map_sub c.mapMatrix 1 N
    rw [map_one] at h
    exact h
  rw [hU, GlobalTheory.WeilM.dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [transpose_add, transpose_sub, transpose_neg, transpose_one, hm1, hm2, hm3]

  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · calc _ = J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = J := by rw [hN, add_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -(Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = 0 := by rw [hN, neg_zero]
  · calc _ = -J + (Nᵀ * J + J * N.map c) := by noncomm_ring
      _ = -J := by rw [hN, add_zero]

theorem cong_block {e : R} {x : Matrix β β A} (hx : (1 - e) • (x - 1) = 0) :
    (1 - e) • (fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1) = 0 := by
  have h1 : fromBlocks x (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) - 1 =
      fromBlocks (x - 1) 0 0 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, fromBlocks_smul, hx]
  simp

theorem decomposition : ∀ (R A : Type) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (c : A →ₐ[R] A) (β : Type) [inst_3 : Fintype β] [inst_4 : DecidableEq β] (J : Matrix β β A), IsUnit (Matrix.det J) →
    ∀ (e : R), e * e = e →
    ∀ (g k : ↥(GlobalTheory.WeilM.UG c J)), ((1 : R) - e) • ((↑(↑g : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ((1 : R) - e) • ((↑(↑k : GL β A) : Matrix β β A) - (1 : Matrix β β A)) = (0 : Matrix β β A) →
    ∀ (a b : Matrix β β A), e • a = a →
    e • b = b →
    a * ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑k : GL β A) : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) = e • (1 : Matrix β β A) →
    ((1 : Matrix β β A) - (↑(↑(g⁻¹ * k) : GL β A) : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ (gd kd : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))), (↑(↑gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑g : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    (↑(↑kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (↑(↑k : GL β A) : Matrix β β A) (0 : Matrix β β A) (0 : Matrix β β A) (1 : Matrix β β A) →
    ∃ (p₁ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (p₂ : ↥(GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J))) (t₁ : GL β A) (t₂ : GL β A), ((1 : R) - e) • ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((1 : R) - e) • ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - (1 : Matrix (β ⊕ β) (β ⊕ β) A)) = (0 : Matrix (β ⊕ β) (β ⊕ β) A) ∧
    ((↑(↑p₁ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₁ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    ((↑(↑p₂ : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) : Matrix (β ⊕ β) β A) = ((GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β A) * (↑t₂ : Matrix β β A) : Matrix (β ⊕ β) β A) ∧
    gd = kd * p₁ * kd⁻¹ * p₂ := by
  intro R A _ _ _ c β _ _ J _ e he g k hg hk a b hea heb hak hka hbh hhb gd kd hgd hkd
  obtain ⟨Km, hKm⟩ : ∃ Km : Matrix β β A, Km = (((k : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  obtain ⟨gi, hgi⟩ : ∃ gi : Matrix β β A, gi = (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) :=
    ⟨_, rfl⟩
  have hKk : Km * ((k : GL β A) : Matrix β β A) = 1 := by rw [hKm]; exact Units.inv_mul _
  have hkK : ((k : GL β A) : Matrix β β A) * Km = 1 := by rw [hKm]; exact Units.mul_inv _
  have hgig : gi * ((g : GL β A) : Matrix β β A) = 1 := by rw [hgi]; exact Units.inv_mul _
  have hggi : ((g : GL β A) : Matrix β β A) * gi = 1 := by rw [hgi]; exact Units.mul_inv _
  have hhgk : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = gi * ((k : GL β A) : Matrix β β A) := by rw [hgi]; rfl

  have hh : (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) * (Km * ((g : GL β A) : Matrix β β A)) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((k : GL β A) : Matrix β β A) Km, hkK, Matrix.one_mul, hgig]
  have hh2 : Km * ((g : GL β A) : Matrix β β A) * (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A) = 1 := by
    rw [hhgk, Matrix.mul_assoc, ← Matrix.mul_assoc ((g : GL β A) : Matrix β β A) gi, hggi, Matrix.one_mul, hKk]
  have hKc : (1 - e) • (Km - 1) = 0 := cong_inv hk hKk
  have hhc : (1 - e) • (Km * ((g : GL β A) : Matrix β β A) - 1) = 0 := cong_mul hKc hg
  have key1 := key hKk hh hKc hhc hka hbh
  have key2 := key hh2 hkK hhc hKc hhb hak

  have hca := cayley c (J := J) (k := ((k : GL β A) : Matrix β β A)) (a := a) k.2 hea hka he
  have hcb := cayley c (J := J) (k := (((g⁻¹ * k : GlobalTheory.WeilM.UG c J) : GL β A) : Matrix β β A)) (a := b) (g⁻¹ * k).2 heb hhb he
  have hskew : (a - b)ᵀ * J + J * (a - b).map c = 0 := by
    have hmap : (a - b).map c = a.map c - b.map c := by ext i j; simp
    rw [transpose_sub, hmap, Matrix.sub_mul, Matrix.mul_sub]
    calc aᵀ * J - bᵀ * J + (J * a.map c - J * b.map c)
        = (aᵀ * J + J * a.map c) - (bᵀ * J + J * b.map c) := by abel
      _ = 0 := by rw [hca, hcb, sub_self]
  obtain ⟨u, hu⟩ : ∃ u : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J),
      ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 + (a - b)) (-(a - b)) (a - b) (1 - (a - b)) ∧
      (((u⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks (1 - (a - b)) (a - b) (-(a - b)) (1 + (a - b)) :=
    ⟨⟨unip (a - b), unip_mem c hskew⟩, rfl, rfl⟩
  have h2 : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := Units.inv_mul _
  have hkdinv : (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks Km 0 0 1 := by
    have h1 : ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1 = 1 := by
      rw [hkd, fromBlocks_multiply, hkK]; simp [fromBlocks_one]
    calc (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks Km 0 0 1) := by rw [h1, Matrix.mul_one]
      _ = fromBlocks Km 0 0 1 := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hblk : ∀ P Q S T : Matrix β β A,
      fromBlocks P Q S T - 1 = fromBlocks (P - 1) Q S (T - 1) := by
    intro P Q S T
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  have hN0 : (1 - e) • (a - b) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hN0' : (1 - e) • (b - a) = 0 := by simp [smul_sub, sub_smul, hea, heb]
  have hkdc : (1 - e) • (((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hkd]; exact cong_block hk
  have hgdc : (1 - e) • (((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by rw [hgd]; exact cong_block hg
  have hkdic : (1 - e) • ((((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := cong_inv hkdc h2
  have huc : (1 - e) • (((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 := by
    rw [hu.1, hblk, fromBlocks_smul]; simp [hN0, hN0']

  have ht : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) = 1 := by
    have e1 : (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) * (1 - (a - b) * (Km - 1)) =
        (1 - (a - b) * (Km - 1)) - (b - a) * ((Km * ((g : GL β A) : Matrix β β A) - 1) * (1 - (a - b) * (Km - 1))) := by
      noncomm_ring
    rw [e1, key2]
    noncomm_ring
  have hK2 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) = (1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b) := by
    have e1 : Km * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) =
        (Km - 1) * (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) + (1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1)) := by
      noncomm_ring
    rw [e1, key1]
    noncomm_ring
  have hfin : ((k : GL β A) : Matrix β β A) * ((1 + (a - b)) * (Km * ((g : GL β A) : Matrix β β A)) - (a - b)) = 1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1) := by
    rw [← hK2, ← Matrix.mul_assoc, hkK, Matrix.one_mul]
  have hv : (((kd * u * kd⁻¹ * gd : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) :
      Matrix (β ⊕ β) (β ⊕ β) A) = ((kd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((u : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * (((kd⁻¹ : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) * ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) := rfl
  refine ⟨u⁻¹, kd * u * kd⁻¹ * gd, 1,
    ⟨1 - (b - a) * (Km * ((g : GL β A) : Matrix β β A) - 1), 1 - (a - b) * (Km - 1), ht, mul_eq_one_comm.mp ht⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hu.2, hblk, fromBlocks_smul]; simp [hN0, hN0']
  · rw [hv]; exact cong_mul (cong_mul (cong_mul hkdc huc) hkdic) hgdc
  · rw [hu.2, GlobalTheory.WeilM.diagCols]
    simp only [fromBlocks_mul_fromRows, fromRows_mul, Units.val_one, Matrix.mul_one,
      Matrix.one_mul]
    rw [fromRows_ext_iff]
    constructor <;> abel
  · rw [hv, hkd, hu.1, hkdinv, hgd, GlobalTheory.WeilM.diagCols]
    simp only [Matrix.mul_assoc, fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Units.val_mk]
    rw [fromRows_ext_iff]
    constructor
    · refine Eq.trans ?_ (hfin.trans ?_) <;> noncomm_ring
    · noncomm_ring
  · group

end GlobalTheory.UnipotentCongruenceInverse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_good_models : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.EvAdm.comp_mem_adm | exact GlobalTheory.EvAdm.comp_mem_adm | (intros; apply GlobalTheory.EvAdm.comp_mem_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  first | exact @GlobalTheory.VacIndic.eventually_isVac_indicator | exact GlobalTheory.VacIndic.eventually_isVac_indicator | (intros; apply GlobalTheory.VacIndic.eventually_isVac_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∃ w₀ ∈ GlobalTheory.DblVac.KD σ W v, ∀ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W →
      w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ W v ∧ w₀ * q * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ W := by
  first | exact @GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | exact GlobalTheory.DblVacFlip.flipPt_conj_anti_diag | (intros; apply GlobalTheory.DblVacFlip.flipPt_conj_anti_diag <;> assumption)
end

