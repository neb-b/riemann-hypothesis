module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LeviMaps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LS

def RestrictAtPoint : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N c : ℕ) (n : Fin c → ℕ)
  (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (X : Type) [AddCommGroup X]
  [Module ℂ X] (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) X)
  (F : PositivityTheory.RSHS.LeviInductionForms.LocMaps (indForms h π) w ρ), F.1 ≠ 0 →
    ∃ L : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ), (∀ v, L v ∈ tensorForms π) ∧ L ≠ 0 ∧
      ∀ (p : parab (w.adicCompletion E) (stdBlocks n h)) (v : X),
        L (ρ p v) = fun m => L v fun i => m i * finGL E (n i)
          (locGL E (n i) w (leviProj (w.adicCompletion E) (stdBlocks n h) p i))

def ExistsProj : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (c : ℕ) (n : Fin c → ℕ)
  (π : ∀ i, CuspSub E (n i)) (w : HeightOneSpectrum (𝓞 E)) (τ : ∀ i, SmIrr (GL (Fin (n i)) (w.adicCompletion E))),
  (∀ i, (π i).IsLocComp w (τ i)) → ∀ t ∈ tensorForms π, t ≠ 0 →
    ∃ p : ((∀ i, GA E (n i)) → ℂ) →ₗ[ℂ] PiTensorProduct ℂ fun i => (τ i).V, p t ≠ 0 ∧
      ∀ (g : ∀ i, GL (Fin (n i)) (w.adicCompletion E)), ∀ s ∈ tensorForms π,
        p (fun m => s fun i => m i * finGL E (n i) (locGL E (n i) w (g i))) = piTensor (fun i => (τ i).ρ) g (p s)

def FrobRecip : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (N c : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N) (σ' : SmIrr (GL (Fin N) k)) (W : Type) [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W) (ℓ : σ'.V →ₗ[ℂ] W), ℓ ≠ 0 →
    (∀ (p : parab k (stdBlocks n h)) (v : σ'.V), ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) →
      ∃ f : σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)),
        f.toLinearMap ≠ 0

end PositivityTheory.RSHS.LS

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ChordArithmetic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem mulChi_absC_cancel (a : ℕ) (z : ℂ) (ψ : Sm E a) :
    mulChi a (Model.absC E z) (mulChi a (Model.absC E (-z)) ψ) = ψ := by
  refine Subtype.ext (funext fun m => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem central_twist {a : ℕ} (w e : ℂ) (h : e + w * a * (Module.finrank ℚ E : ℂ) = 0) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) = (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl]
  have e1 : Complex.exp (e * t) * Complex.exp (w * a * (Module.finrank ℚ E : ℂ) * t) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    linear_combination (t : ℂ) * h
  linear_combination (ψ.1 m * ((chiDet a (Model.absC E w) m : ℂˣ) : ℂ)) * e1

theorem left_eq (c c₁ : ℂ) (r r₁ d : ℕ) (hr : r ≠ 0) (hd : d ≠ 0) :
    (c₁ - -(c / (r * d)) * r₁ * d).re = c₁.re + (r₁ : ℝ) / r * c.re := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c₁ - -(c / (r * d)) * r₁ * d = c₁ + (((r₁ : ℝ) / r : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem right_eq (c c₂ : ℂ) (s r₂ d : ℕ) (hs : s ≠ 0) (hd : d ≠ 0) :
    (c + (c₂ - -(-c / (s * d)) * r₂ * d)).re = c₂.re + ((s : ℝ) - r₂) / s * c.re := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have e : c + (c₂ - -(-c / (s * d)) * r₂ * d) = c₂ + ((((s : ℝ) - r₂) / s : ℝ) : ℂ) * c := by
    push_cast
    field_simp
    ring
  rw [e, Complex.add_re, Complex.re_ofReal_mul]

theorem left_arith (r s r₁ d lam x y : ℝ) (hr : 0 < r) (h1 : 0 < r₁) (h2 : r₁ < r) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + r₁ / r * y) / d - r₁ * (r + s - r₁) / 2 ≤ -lam * (r₁ * (r + s - r₁))) :
    x / d - r₁ * (r - r₁) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + r₁ / r * y) / d = x / d + r₁ / r * (y / d) := by ring
  have e2 : r₁ / r * (r * s / 2 - lam * (r * s)) = r₁ * s / 2 - lam * (r₁ * s) := by field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

theorem right_arith (r s r₂ d lam x y : ℝ) (hs : 0 < s) (h1 : 0 < r₂) (h2 : r₂ < s) (hlam : 0 < lam)
    (hp : y / d - r * (r + s - r) / 2 = -lam * (r * s))
    (hb : (x + (s - r₂) / s * y) / d - (r + r₂) * (r + s - (r + r₂)) / 2 ≤ -lam * ((r + r₂) * (r + s - (r + r₂)))) :
    x / d - r₂ * (s - r₂) / 2 < 0 := by
  have hY : y / d = r * s / 2 - lam * (r * s) := by linarith
  have e : (x + (s - r₂) / s * y) / d = x / d + (s - r₂) / s * (y / d) := by ring
  have e2 : (s - r₂) / s * (r * s / 2 - lam * (r * s)) = r * (s - r₂) / 2 - lam * (r * (s - r₂)) := by
    field_simp
  rw [e, hY, e2] at hb
  nlinarith [mul_pos hlam (mul_pos h1 (sub_pos.2 h2))]

end PositivityTheory.Rg.Rs.ChordArithmetic
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

theorem expTw_holds : ExpTw := by
  intro E _ _ _ N φ z _ r _ hrN c hc
  let _ : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨F₀, ⟨μ, 𝓕, hμ, h𝓕, hF₀⟩, F, hF, hF0, hFt⟩ := hc
  set χ := Model.absC E z
  set Y : GA E N → ℂ := fun g => (((chiDet N χ g)⁻¹ : ℂˣ) : ℂ) with hY
  have hu : ∀ (x : BlockIx N r → Ad E), chiDet N χ (unip x) = 1 := fun x => by
    change (χ : GlobalTheory.Mem.Chr.Ideles E →* ℂˣ) (Matrix.GeneralLinearGroup.det (unip x)) = 1
    rw [det_unip, map_one]
  have hct : F₀ = fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 g * ((chiDet N χ g : ℂˣ) : ℂ) := by
    rw [hF₀]
    funext g
    simp only [PositivityTheory.Affgl.CT.ct]
    rw [← integral_mul_const]
    congr 1
    funext x
    rw [mulChi_apply, map_mul, hu, one_mul]
  have hYX : ∀ g, ((chiDet N χ g : ℂˣ) : ℂ) * Y g = 1 := fun g => Units.mul_inv _
  have hYa : ∀ t : ℝ, Y (aT E N r t) = Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := fun t => by
    simp only [hY]
    rw [Units.val_inv_eq_inv_val, ExponentTwist.chiDet_aT hrN.le, ← Complex.exp_neg]
  refine ⟨PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1, ⟨μ, 𝓕, hμ, h𝓕, rfl⟩, LinearMap.mulRight ℂ Y F, ?_, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := LinearMap.mulRight ℂ Y) hF
    rw [Submodule.map_span] at h1
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    have e : LinearMap.mulRight ℂ Y (fun g => F₀ (aT E N r t * g)) =
        ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ) • fun g => PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) := by
      funext g
      simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hct, map_mul, Units.val_mul]
      linear_combination (PositivityTheory.Affgl.CT.ct μ 𝓕 φ.1 (aT E N r t * g) * ((chiDet N χ (aT E N r t) : ℂˣ) : ℂ)) * hYX g
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · intro h
    apply hF0
    funext g
    have h2 := congrFun h g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply, Pi.zero_apply] at h2
    have h3 : Y g ≠ 0 := Units.ne_zero _
    exact (mul_eq_zero.1 h2).resolve_right h3
  · intro t g
    simp only [LinearMap.mulRight_apply, Pi.mul_apply]
    have hYm : ∀ a b, Y (a * b) = Y a * Y b := fun a b => by simp only [hY, map_mul, mul_inv, Units.val_mul]
    have e : Complex.exp ((c - z * r * (Module.finrank ℚ E : ℂ)) * t) =
        Complex.exp (c * t) * Complex.exp (-(z * r * (Module.finrank ℚ E : ℂ) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hFt, hYm, hYa, e]
    ring

end PositivityTheory.Rg.Rs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ParabolicProjection

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem mulChi_absC_neg (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) φ) = φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

theorem mulChi_absC_neg' (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E (-z)) φ) = φ := by
  have h := mulChi_absC_neg n (-z) φ
  rwa [neg_neg] at h

theorem isStable_tw {n : ℕ} {U : Submodule ℂ (Sm E n)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (z : ℂ) : _root_.GlobalTheory.CuspRep.IsStable (tw U z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (hU o φ hφ)) (U.smul_mem _ hφ), (act_mulChi _ o φ).symm⟩

def twMap (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) : Sm E n →ₗ[ℂ] Sm E n :=
  (mulChi n (Model.absC E z)).toLinearMap ∘ₗ f ∘ₗ (mulChi n (Model.absC E (-z))).toLinearMap

theorem twMap_apply (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) (φ : Sm E n) :
    twMap n z f φ = mulChi n (Model.absC E z) (f (mulChi n (Model.absC E (-z)) φ)) := rfl

theorem twMap_equiv {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} (_hU : _root_.GlobalTheory.CuspRep.IsStable U) {f : Sm E n →ₗ[ℂ] Sm E n}
    (hf : ∀ o, ∀ ψ ∈ U, f (act o ψ) = act o (f ψ)) : ∀ o, ∀ ψ ∈ tw U z, twMap n z f (act o ψ) = act o (twMap n z f ψ) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  change twMap n z f (act o (mulChi n (Model.absC E z) φ)) = act o (twMap n z f (mulChi n (Model.absC E z) φ))
  rw [twMap_apply, twMap_apply, mulChi_absC_neg, act_mulChi, mulChi_absC_neg, map_add (f := _), map_smul, map_smul, hf o φ hφ,
    act_mulChi]

theorem twMap_mem {n : ℕ} {z : ℂ} {U W : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ ∈ W) :
    ∀ ψ ∈ tw U z, twMap n z f ψ ∈ tw W z := by
  rintro _ ⟨φ, hφ, rfl⟩
  change twMap n z f (mulChi n (Model.absC E z) φ) ∈ tw W z
  rw [twMap_apply, mulChi_absC_neg]
  exact ⟨_, hf φ hφ, rfl⟩

theorem twMap_ne {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ = 0 → ψ = 0) :
    ∀ ψ ∈ tw U z, twMap n z f ψ = 0 → ψ = 0 := by
  rintro _ ⟨φ, hφ, rfl⟩ h
  change twMap n z f (mulChi n (Model.absC E z) φ) = 0 at h
  rw [twMap_apply, mulChi_absC_neg, LinearEquiv.map_eq_zero_iff] at h
  change mulChi n (Model.absC E z) φ = 0
  rw [hf φ hφ h, map_zero]

variable {r s : ℕ}

theorem tensor_pair_finite_sum {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 V₁ V₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ V₁) ∧ (∀ i, ψ₂ i ∈ V₂) ∧
      ∀ m, F m = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨1, fun _ => φ₁, fun _ => φ₂, fun _ => h₁, fun _ => h₂, fun m => by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun m => by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    obtain ⟨n', b₁, b₂, hb₁, hb₂, hb⟩ := hG
    refine ⟨n + n', Fin.append a₁ b₁, Fin.append a₂ b₂, fun i => ?_, fun i => ?_, fun m => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₁ j
      · simpa using hb₁ j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₂ j
      · simpa using hb₂ j
    · simp [Fin.sum_univ_add, ha, hb]
  | smul c F _ hF =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    exact ⟨n, fun i => c • a₁ i, a₂, fun i => Submodule.smul_mem _ c (ha₁ i), ha₂, fun m => by
      simp [ha, Finset.mul_sum, mul_assoc]⟩

theorem sum_mem_tens2 {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ V₁) (h₂ : ∀ i, ψ₂ i ∈ V₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 V₁ V₂ := by
  have e : (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      ∑ i, fun m : GA E r × GA E s => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
    funext m
    simp [Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨ψ₁ i, h₁ i, ψ₂ i, h₂ i, rfl⟩

theorem exists_decomp (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g' : GL (Fin (r + s)) (Af E)), g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨x, m, t, k, l, -, -, rfl⟩ := hT g
  refine ⟨x, m, k, t * l, ?_⟩
  rw [map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

theorem exists_slice_ne {F : Sm E (r + s)} (hF : F ≠ 0) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∃ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hF
  apply Subtype.ext
  funext g
  obtain ⟨x, m, k, g', rfl⟩ := exists_decomp g
  rw [mul_assoc, hu, hcon k g' m]
  rfl

theorem sum_left_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₂ i).1 m₂ • ψ₁ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E r => φ.1 m₁) h0
  simpa [Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

theorem sum_right_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₁ i).1 m₁ • ψ₂ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E s => φ.1 m₂) h0
  simpa [Submodule.coe_sum, Finset.sum_apply] using this

theorem step_left {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₂ : GA E s} (f : Sm E r →ₗ[ℂ] Sm E r)
    (h : f (∑ i, (ψ₂ i).1 m₂ • ψ₁ i) ≠ 0) : ∃ b₁, ∑ i, (f (ψ₁ i)).1 b₁ * (ψ₂ i).1 m₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

theorem step_right {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} (f : Sm E s →ₗ[ℂ] Sm E s)
    (h : f (∑ i, (ψ₁ i).1 m₁ • ψ₂ i) ≠ 0) : ∃ b₂, ∑ i, (ψ₁ i).1 m₁ * (f (ψ₂ i)).1 b₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, Submodule.coe_sum, Finset.sum_apply] using this

theorem inj_of_irred {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {T : Sm E N →ₗ[ℂ] Sm E N}
    (hT : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (hne : ∃ φ ∈ V, T φ ≠ 0) : ∀ φ ∈ V, T φ = 0 → φ = 0 := by
  intro φ hφ h0
  have hW : _root_.GlobalTheory.CuspRep.IsStable (V ⊓ LinearMap.ker T) := fun o ψ hψ => by
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hψ ⊢
    exact ⟨hV.stable o ψ hψ.1, by rw [hT o ψ hψ.1, hψ.2, map_zero]⟩
  rcases hV.irred _ inf_le_left hW with h | h
  · have hm : φ ∈ V ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hφ, h0⟩
    rw [h] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · obtain ⟨ψ, hψ, hne⟩ := hne
    exact absurd (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (h.ge hψ)).2) hne

end PositivityTheory.Rg.Rs.ParabolicProjection

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.LFun GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem finRep_mulChi {m : ℕ} (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin m) (w.adicCompletion E))
    (x : Sm E m) :
    finRep E m (locGL E m w g) (mulChi m χ x) =
      ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • mulChi m χ (finRep E m (locGL E m w g) x) := by
  have := act_mulChi (o := (Op.fin (locGL E m w g) : Op E m)) χ x
  rw [opAdd, zero_smul, add_zero, opMul, CuspSub.chiDet_locGL, map_smul] at this
  exact this

theorem satLike_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatLike V w B) :
    SatLike (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  intro ψ hψ hK h0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
  have hxK : ∀ k ∈ KGL w (n := m), finRep E m (locGL E m w k) x = x := fun k hk => by
    have e := hK k hk
    rw [LinearEquiv.coe_coe, finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one,
      one_smul] at e
    exact (mulChi m χ).injective e
  have hx0 : x ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hs := h x hx hxK hx0
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK k hk, by rw [Multiset.card_map, hs.2.2.1],
    fun ϖ hϖ j hj => ?_⟩
  rw [LinearEquiv.coe_coe, GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← map_smul (mulChi m χ),
    ← hs.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
  have e := (mulChi m χ).toAddEquiv.map_finsum
    (fun c : _ ⧸ KGL w (n := m) => Tj ℂ m (Ov E w) ϖ j c.out • ((finRep E m).comp (locGL E m w)) c.out x)
  rw [show (mulChi m χ) _ = _ from e, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
  · simp [hc]
  · change Tj ℂ m (Ov E w) ϖ j c.out • finRep E m (locGL E m w c.out) (mulChi m χ x) = _
    rw [finRep_mulChi, GlobalTheory.SphGal.loc_det_of_Tj hχ hϖ hj hc, smul_comm]
    simp

open GlobalTheory.Mem.Chr.CharModel in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem unrAt_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).UnrAt w := fun x hx => Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [logNorm_local w x 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]; simp)

open GlobalTheory.Mem.Chr.CharModel in
theorem val_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).val w = qU w (-s) := Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [qU_val, logNorm_local w _ 1 (Formalism.L2.Host.unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring)

theorem satLike_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatLike V w B) (z : ℂ) : SatLike (tw V z) w (B.map (· * qU w (-z))) := by
  have := satLike_map_mulChi (unrAt_absC z w) h
  rw [val_absC] at this
  exact this

end PositivityTheory.Rg.Rs.SatakeVectors

end
end

